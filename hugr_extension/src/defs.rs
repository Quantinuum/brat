use std::str::FromStr;

use crate::{closure_custom_type, closure_type, ctor::BratCtor};
use enum_iterator::Sequence;
use hugr::{
    extension::{
        prelude::{QB_T, USIZE_T},
        simple_op::{MakeOpDef, OpLoadError},
        ExtensionId, OpDef, SignatureError, SignatureFromArgs, SignatureFunc,
    },
    std_extensions::arithmetic::int_types::INT_TYPES,
    std_extensions::arithmetic::float_types::FLOAT64_TYPE,
    std_extensions::collections::list_type,
    types::{
        type_param::TypeParam, FuncValueType, PolyFuncTypeRV, Signature, Type, TypeArg, TypeBound,
        TypeEnum, TypeRV, TypeRow,
    },
};

use lazy_static::lazy_static;

use smol_str::format_smolstr;
use strum::ParseError;

use crate::ctor::Ctor;

lazy_static! {
    static ref U64: Type = INT_TYPES[6].clone();
}

/// Brat extension operation definitions.
#[derive(Clone, Debug, PartialEq, Eq, Sequence)]
#[allow(missing_docs)]
pub enum BratOpDef {
    Hole,
    Substitute,
    MakeClosure,
    ClosureCall,
    Partial,
    Panic,
    Ctor(BratCtor),
    PrimCtorTest(BratCtor),
    Lluf,
    Replicate,
    CRx,
    CRy,
    CRz,
}

impl FromStr for BratOpDef {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let v: Vec<_> = s.splitn(2, "::").collect();
        match v.as_slice() {
            ["Hole"] => Ok(BratOpDef::Hole),
            ["Substitute"] => Ok(BratOpDef::Substitute),
            ["MakeClosure"] => Ok(BratOpDef::MakeClosure),
            ["ClosureCall"] => Ok(BratOpDef::ClosureCall),
            ["Partial"] => Ok(BratOpDef::Partial),
            ["Panic"] => Ok(BratOpDef::Panic),
            ["Ctor", ctor] => Ok(BratOpDef::Ctor(BratCtor::from_str(ctor)?)),
            ["PrimCtorTest", ctor] => Ok(BratOpDef::PrimCtorTest(BratCtor::from_str(ctor)?)),
            ["Lluf"] => Ok(BratOpDef::Lluf),
            ["Replicate"] => Ok(BratOpDef::Replicate),
            ["CRx"] => Ok(BratOpDef::CRx),
            ["CRy"] => Ok(BratOpDef::CRy),
            ["CRz"] => Ok(BratOpDef::CRz),
            _ => Err(ParseError::VariantNotFound),
        }
    }
}

impl MakeOpDef for BratOpDef {
    fn opdef_id(&self) -> smol_str::SmolStr {
        use BratOpDef::*;
        match self {
            Hole => "Hole".into(),
            Substitute => "Substitute".into(),
            MakeClosure => "MakeClosure".into(),
            ClosureCall => "ClosureCall".into(),
            Partial => "Partial".into(),
            Panic => "Panic".into(),
            Ctor(ctor) => format_smolstr!("Ctor::{}", ctor.name()),
            PrimCtorTest(ctor) => format_smolstr!("PrimCtorTest::{}", ctor.name()),
            Lluf => "Lluf".into(),
            Replicate => "Replicate".into(),
        }
    }

    fn extension_ref(&self) -> std::sync::Weak<hugr::Extension> {
        std::sync::Weak::new()
    }

    fn from_def(op_def: &OpDef) -> Result<Self, OpLoadError> {
        hugr::extension::simple_op::try_from_name(op_def.name(), &super::EXTENSION_ID)
    }

    fn init_signature(&self, extension_ref: &std::sync::Weak<hugr::Extension>) -> SignatureFunc {
        use BratOpDef::*;
        match self {
            Hole => SignatureFunc::CustomFunc(Box::new(HoleSigFun)),
            Substitute => SignatureFunc::CustomFunc(Box::new(SubstituteSigFun)),
            MakeClosure => {
                // (*S -> *T) -> Closure<S, T>
                let func_ty = Type::new_function(FuncValueType::new(
                    vec![TypeRV::new_row_var_use(0, TypeBound::Linear)],
                    vec![TypeRV::new_row_var_use(1, TypeBound::Linear)],
                ));
                let closure_ty = closure_custom_type(
                    vec![TypeRV::new_row_var_use(0, TypeBound::Linear)],
                    vec![TypeRV::new_row_var_use(1, TypeBound::Linear)],
                    extension_ref,
                );
                let output_row = TypeRow::new().extend(vec![&Type::from(closure_ty)]);
                let x = PolyFuncTypeRV::new(
                    vec![list_of_type(), list_of_type()],
                    FuncValueType::new(vec![func_ty], output_row),
                )
                .into();
                x
            }
            ClosureCall => {
                // Closure<S, T>, *S -> *T
                let closure_ty = closure_custom_type(
                    vec![TypeRV::new_row_var_use(0, TypeBound::Linear)],
                    vec![TypeRV::new_row_var_use(1, TypeBound::Linear)],
                    extension_ref,
                );
                let x = PolyFuncTypeRV::new(
                    vec![list_of_type(), list_of_type()],
                    FuncValueType::new(
                        vec![
                            Type::from(closure_ty).into(),
                            TypeRV::new_row_var_use(0, TypeBound::Linear),
                        ],
                        vec![TypeRV::new_row_var_use(1, TypeBound::Linear)],
                    ),
                )
                .into();
                x
            }
            Partial => SignatureFunc::CustomFunc(Box::new(PartialSigFun)),
            Panic => SignatureFunc::CustomFunc(Box::new(PanicSigFun)),
            Ctor(ctor) => ctor.signature().into(),
            PrimCtorTest(ctor) => {
                let sig = ctor.signature();
                let input = sig.body().output(); // Ctor output is input for the test
                let output = Type::new_sum(vec![input.clone(), sig.body().input().clone()]);
                PolyFuncTypeRV::new(
                    sig.params(),
                    FuncValueType::new(input.clone(), vec![output]),
                )
                .into()
            }
            Lluf => Signature::new(vec![U64.clone()], vec![U64.clone()]).into(),
            Replicate => PolyFuncTypeRV::new(
                [TypeParam::RuntimeType(TypeBound::Copyable)],
                FuncValueType::new(
                    vec![
                        prelude::usize_t(),
                        Type::new_var_use(0, TypeBound::Copyable),
                    ],
                    vec![list_type(Type::new_var_use(0, TypeBound::Copyable))],
                ),
            )
                .into(),
            CRx => Signature::new(vec![QB_T, QB_T, FLOAT64_TYPE], vec![QB_T, QB_T]).into(),
            CRy => Signature::new(vec![QB_T, QB_T, FLOAT64_TYPE], vec![QB_T, QB_T]).into(),
            CRz => Signature::new(vec![QB_T, QB_T, FLOAT64_TYPE], vec![QB_T, QB_T]).into(),
        }
    }

    fn extension(&self) -> ExtensionId {
        super::EXTENSION_ID.clone()
    }
}

/// Binary compute_signature function for the `Hole` op
struct HoleSigFun;
impl SignatureFromArgs for HoleSigFun {
    fn compute_signature(&self, arg_values: &[TypeArg]) -> Result<PolyFuncTypeRV, SignatureError> {
        // The Hole op expects a nat identifier and two type sequences specifiying
        // the signature of the hole
        match arg_values {
            [TypeArg::BoundedNat(_), TypeArg::Runtime(fun_ty)] => {
                let TypeEnum::Function(sig) = fun_ty.as_type_enum().clone() else {
                    return Err(SignatureError::InvalidTypeArgs);
                };
                Ok(PolyFuncTypeRV::new([], *sig))
            }
            _ => Err(SignatureError::InvalidTypeArgs),
        }
    }

    fn static_params(&self) -> &[TypeParam] {
        lazy_static! {
            static ref PARAMS: [TypeParam; 2] = [
                TypeParam::max_nat_type(),
                TypeParam::RuntimeType(TypeBound::Linear)
            ];
        }
        PARAMS.as_slice()
    }
}

/// Binary compute_signature function for the `Substitute` op
struct SubstituteSigFun;
impl SignatureFromArgs for SubstituteSigFun {
    fn compute_signature(&self, arg_values: &[TypeArg]) -> Result<PolyFuncTypeRV, SignatureError> {
        // The Substitute op expects a function signature and a list of hole signatures
        match arg_values {
            [TypeArg::Runtime(outer_fun_ty), TypeArg::List(hole_sigs)] => {
                let mut inputs = vec![outer_fun_ty.clone()];
                for sig in hole_sigs {
                    let TypeArg::Runtime(inner_fun_ty) = sig else {
                        return Err(SignatureError::InvalidTypeArgs);
                    };
                    inputs.push(inner_fun_ty.clone())
                }
                Ok(FuncValueType::new(inputs, vec![outer_fun_ty.clone()]).into())
            }
            _ => Err(SignatureError::InvalidTypeArgs),
        }
    }

    fn static_params(&self) -> &[TypeParam] {
        lazy_static! {
            static ref PARAMS: [TypeParam; 2] = [
                // The signature of outer functions
                TypeParam::RuntimeType(TypeBound::Linear),
                // A list of signatures for the inner functions which fill in holes
                TypeParam::ListType(Box::new(TypeParam::RuntimeType(TypeBound::Linear))),
            ];
        }
        PARAMS.as_slice()
    }
}

/// Binary compute_signature function for the `Partial` op
struct PartialSigFun;
impl SignatureFromArgs for PartialSigFun {
    fn compute_signature(&self, arg_values: &[TypeArg]) -> Result<PolyFuncTypeRV, SignatureError> {
        // The Partial op expects a type sequence specifying the supplied partial inputs, a type
        // sequence specifiying the remaining inputs and a type sequence for the function outputs.
        match arg_values {
            [partial_inputs, other_inputs, outputs] => {
                let partial_inputs = row_from_arg(partial_inputs)?;
                let other_inputs = row_from_arg(other_inputs)?;
                let outputs = row_from_arg(outputs)?;
                let res_func = closure_type(other_inputs.clone(), outputs.clone());
                let mut inputs =
                    vec![
                        closure_type([partial_inputs.clone(), other_inputs].concat(), outputs)
                            .into(),
                    ];
                inputs.extend(partial_inputs);
                Ok(FuncValueType::new(inputs, vec![res_func]).into())
            }
            _ => Err(SignatureError::InvalidTypeArgs),
        }
    }

    fn static_params(&self) -> &[TypeParam] {
        lazy_static! {
            static ref PARAMS: [TypeParam; 3] = [list_of_type(), list_of_type(), list_of_type()];
        }
        PARAMS.as_slice()
    }
}

/// Binary compute_signature function for the `Panic` op
struct PanicSigFun;
impl SignatureFromArgs for PanicSigFun {
    fn compute_signature(&self, arg_values: &[TypeArg]) -> Result<PolyFuncTypeRV, SignatureError> {
        // The Panic op expects two type sequences specifiying the signature of the op
        match arg_values {
            [input, output] => {
                Ok(FuncValueType::new(row_from_arg(input)?, row_from_arg(output)?).into())
            }
            _ => Err(SignatureError::InvalidTypeArgs),
        }
    }

    fn static_params(&self) -> &[TypeParam] {
        lazy_static! {
            static ref PARAMS: [TypeParam; 2] = [
                TypeParam::ListType(Box::new(TypeParam::RuntimeType(TypeBound::Linear))),
                TypeParam::ListType(Box::new(TypeParam::RuntimeType(TypeBound::Linear))),
            ];
        }
        PARAMS.as_slice()
    }
}

fn row_from_arg(arg: &TypeArg) -> Result<Vec<TypeRV>, SignatureError> {
    match arg {
        TypeArg::List(elems) => elems
            .iter()
            .map(|arg| match arg {
                TypeArg::Runtime(ty) => Ok(ty.clone().into()),
                _ => Err(SignatureError::InvalidTypeArgs),
            })
            .collect(),
        _ => Err(SignatureError::InvalidTypeArgs),
    }
}

fn list_of_type() -> TypeParam {
    TypeParam::ListType(Box::new(TypeParam::RuntimeType(TypeBound::Linear)))
}
