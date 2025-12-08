use hugr::{
    extension::{
        simple_op::{MakeExtensionOp, MakeOpDef, OpLoadError},
        SignatureError,
    },
    ops::{custom::ExtensionOp, NamedOp, OpTrait},
    types::{Signature, Type, TypeArg, TypeEnum, TypeRow},
};
use smol_str::{format_smolstr, SmolStr};

use crate::{ctor::BratCtor, defs::BratOpDef};

/// Brat extension ops.
#[derive(Clone, Debug, PartialEq)]
#[allow(missing_docs)]
pub enum BratOp {
    Hole {
        idx: u64,
        sig: Signature,
    },
    Substitute {
        func_sig: Signature,
        hole_sigs: Vec<Signature>,
    },
    MakeClosure {
        sig: Signature,
    },
    ClosureCall {
        sig: Signature,
    },
    Partial {
        inputs: TypeRow,
        output_sig: Signature,
    },
    Panic {
        sig: Signature,
    },
    Ctor {
        ctor: BratCtor,
        args: Vec<TypeArg>,
    },
    PrimCtorTest {
        ctor: BratCtor,
        args: Vec<TypeArg>,
    },
    // The inverse operation of "full" on Nats
    Lluf,
    Replicate(TypeArg),
}

impl NamedOp for BratOp {
    fn name(&self) -> SmolStr {
        use BratOp::*;
        match self {
            Hole { .. } => "Hole".into(),
            Substitute { .. } => "Substitute".into(),
            MakeClosure { .. } => "MakeClosure".into(),
            ClosureCall { .. } => "ClosureCall".into(),
            Partial { .. } => "Partial".into(),
            Panic { .. } => "Panic".into(),
            Ctor { ctor, .. } => format_smolstr!("Ctor::{}", ctor.name()),
            PrimCtorTest { ctor, .. } => format_smolstr!("PrimCtorTest::{}", ctor.name()),
            Lluf => "Lluf".into(),
            Replicate(_) => "Replicate".into(),
        }
    }
}

impl MakeExtensionOp for BratOp {
    fn from_extension_op(ext_op: &ExtensionOp) -> Result<Self, OpLoadError> {
        let def = BratOpDef::from_def(ext_op.def())?;
        let sig = ext_op
            .dataflow_signature()
            .ok_or(OpLoadError::InvalidArgs(SignatureError::InvalidTypeArgs))?;
        match def {
            BratOpDef::Hole => match *ext_op.args() {
                [TypeArg::BoundedNat { n: idx }, ..] => Ok(BratOp::Hole { idx, sig }),
                _ => Err(SignatureError::InvalidTypeArgs.into()),
            },
            BratOpDef::Substitute => match sig.input().as_ref() {
                [func_sig, hole_sigs @ ..] => {
                    let TypeEnum::Function(func_sig) = func_sig.as_type_enum() else {
                        return Err(SignatureError::InvalidTypeArgs.into());
                    };
                    let hole_sigs: Result<Vec<_>, OpLoadError> = hole_sigs
                        .iter()
                        .map(|ty| match ty.as_type_enum() {
                            TypeEnum::Function(f) => Ok(*f.clone()),
                            _ => Err(SignatureError::InvalidTypeArgs.into()),
                        })
                        .collect();
                    let closed_sig = Signature::try_from(*func_sig.clone())
                        .map_err(|_| SignatureError::InvalidTypeArgs)?;

                    let closed_hole_sigs: Result<Vec<Signature>, SignatureError> = hole_sigs?
                        .iter()
                        .map(|a| {
                            Signature::try_from(a.clone())
                                .map_err(|_| SignatureError::InvalidTypeArgs)
                        })
                        .collect();

                    Ok(BratOp::Substitute {
                        func_sig: closed_sig,
                        hole_sigs: closed_hole_sigs?,
                    })
                }
                _ => Err(OpLoadError::InvalidArgs(SignatureError::InvalidTypeArgs)),
            },
            BratOpDef::MakeClosure => match sig.input().as_ref() {
                [func_ty] => {
                    let TypeEnum::Function(func_ty) = func_ty.as_type_enum() else {
                        return Err(SignatureError::InvalidTypeArgs.into());
                    };
                    let sig = Signature::try_from(*func_ty.clone())
                        .map_err(|_| SignatureError::InvalidTypeArgs)?;
                    Ok(BratOp::MakeClosure { sig })
                }
                _ => Err(SignatureError::InvalidTypeArgs.into()),
            },
            BratOpDef::ClosureCall => match sig.input().as_ref() {
                [closure_ty, ..] => Ok(BratOp::ClosureCall {
                    sig: sig_from_closure_ty(closure_ty)?,
                }),
                _ => Err(SignatureError::InvalidTypeArgs.into()),
            },
            BratOpDef::Partial => match (sig.input().as_ref(), sig.output().as_ref()) {
                ([_, partial_inputs @ ..], [output_closure]) => Ok(BratOp::Partial {
                    inputs: partial_inputs.to_vec().into(),
                    output_sig: sig_from_closure_ty(output_closure)?,
                }),
                _ => Err(OpLoadError::InvalidArgs(SignatureError::InvalidTypeArgs)),
            },
            BratOpDef::Panic => Ok(BratOp::Panic { sig }),
            BratOpDef::Ctor(ctor) => Ok(BratOp::Ctor {
                ctor,
                args: ext_op.args().to_vec(),
            }),
            BratOpDef::PrimCtorTest(ctor) => Ok(BratOp::PrimCtorTest {
                ctor,
                args: ext_op.args().to_vec(),
            }),
            BratOpDef::Lluf => Ok(BratOp::Lluf),
            BratOpDef::Replicate => Ok(BratOp::Replicate(ext_op.args()[0].clone())),
        }
    }

    fn type_args(&self) -> Vec<TypeArg> {
        match self {
            BratOp::Hole { idx, sig } => vec![
                TypeArg::BoundedNat { n: *idx },
                TypeArg::Type {
                    ty: Type::new_function(sig.clone()),
                },
            ],
            BratOp::Substitute {
                func_sig,
                hole_sigs,
            } => vec![
                TypeArg::Type {
                    ty: Type::new_function(func_sig.clone()),
                },
                TypeArg::Sequence {
                    elems: hole_sigs
                        .iter()
                        .map(|sig| TypeArg::Type {
                            ty: Type::new_function(sig.clone()),
                        })
                        .collect(),
                },
            ],
            BratOp::Partial { inputs, output_sig } => vec![
                arg_from_row(inputs),
                arg_from_row(output_sig.input()),
                arg_from_row(output_sig.output()),
            ],
            BratOp::Panic { sig } | BratOp::MakeClosure { sig } | BratOp::ClosureCall { sig } => {
                vec![arg_from_row(sig.input()), arg_from_row(sig.output())]
            }
            BratOp::Ctor { args, .. } => args.clone(),
            BratOp::PrimCtorTest { args, .. } => args.clone(),
            BratOp::Lluf => vec![],
            BratOp::Replicate(arg) => vec![arg.clone()],
        }
    }
}

fn arg_from_row(row: &TypeRow) -> TypeArg {
    TypeArg::Sequence {
        elems: row
            .iter()
            .map(|ty| TypeArg::Type { ty: ty.clone() })
            .collect(),
    }
}

fn row_from_args(args: &[TypeArg]) -> Result<Vec<Type>, SignatureError> {
    args.iter()
        .map(|arg| match arg {
            TypeArg::Type { ty } => Ok(ty.clone()),
            _ => Err(SignatureError::InvalidTypeArgs),
        })
        .collect()
}

fn sig_from_closure_ty(ty: &Type) -> Result<Signature, SignatureError> {
    let TypeEnum::Extension(closure_ty) = ty.as_type_enum() else {
        return Err(SignatureError::InvalidTypeArgs);
    };
    let [TypeArg::Sequence { elems: ins }, TypeArg::Sequence { elems: outs }] = closure_ty.args()
    else {
        return Err(SignatureError::InvalidTypeArgs);
    };
    Ok(Signature::new(row_from_args(ins)?, row_from_args(outs)?))
}
