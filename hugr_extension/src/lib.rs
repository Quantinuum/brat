pub mod ctor;
pub mod defs;
pub mod ops;

use enum_iterator::all;
use hugr::{
    extension::{
        prelude,
        simple_op::{MakeOpDef, MakeRegisteredOp},
        ExtensionId, ExtensionRegistry, ExtensionSet, TypeDefBound,
    },
    std_extensions::{arithmetic::int_types, collections},
    types::{type_param::TypeParam, CustomType, Type, TypeArg, TypeBound, TypeName, TypeRV},
    Extension,
};

use lazy_static::lazy_static;

use crate::defs::BratOpDef;

/// Reported unique name of the Brat extension
pub const EXTENSION_ID: ExtensionId = ExtensionId::new_unchecked("Brat");

/// Name of the Brat closure type
pub const CLOSURE_TYPE_ID: TypeName = TypeName::new_inline("Closure");

lazy_static! {
    /// Extension for Brat operations.
    pub static ref EXTENSION: Extension = {
        let reqs = ExtensionSet::from_iter([int_types::EXTENSION_ID, collections::EXTENSION_NAME]);

        let mut extension = Extension::new_with_reqs(EXTENSION_ID, reqs);

        for op in all::<BratOpDef>() {
            op.add_to_extension(&mut extension).unwrap();
        }

        extension.add_type(
            CLOSURE_TYPE_ID,
            vec![TypeParam::new_list(TypeBound::Any), TypeParam::new_list(TypeBound::Any)],
            "Function closure".to_string(),
            TypeDefBound::Explicit(TypeBound::Copyable)
        ).unwrap();

        extension
    };

    /// Registry of extensions required to validate Brat operations.
    pub static ref BRAT_OPS_REGISTRY: ExtensionRegistry  = ExtensionRegistry::try_new([
        prelude::PRELUDE.to_owned(),
        int_types::EXTENSION.to_owned(),
        collections::EXTENSION.to_owned(),
        EXTENSION.to_owned(),
    ])
    .unwrap();
}

impl MakeRegisteredOp for BratOpDef {
    fn extension_id(&self) -> ExtensionId {
        EXTENSION_ID.to_owned()
    }

    fn registry<'s, 'r: 's>(&'s self) -> &'r ExtensionRegistry {
        &BRAT_OPS_REGISTRY
    }
}

/// The function closure type.
pub fn closure_custom_type(ins: Vec<TypeRV>, outs: Vec<TypeRV>) -> CustomType {
    CustomType::new(
        CLOSURE_TYPE_ID,
        [
            TypeArg::Sequence {
                elems: ins.into_iter().map(|ty| ty.into()).collect(),
            },
            TypeArg::Sequence {
                elems: outs.into_iter().map(|ty| ty.into()).collect(),
            },
        ],
        EXTENSION_ID,
        TypeBound::Copyable,
    )
}

/// The function closure type.
///
/// Constructed from [closure_custom_type].
pub fn closure_type(ins: Vec<TypeRV>, outs: Vec<TypeRV>) -> Type {
    closure_custom_type(ins, outs).into()
}

#[cfg(test)]
mod test {
    use hugr::{
        extension::simple_op::MakeExtensionOp,
        ops::{custom::ExtensionOp, NamedOp},
        types::{type_param::TypeParam, Signature, Type, TypeArg},
    };

    use crate::{
        ctor::{BratCtor, Ctor},
        ops::BratOp,
    };

    use super::*;

    #[test]
    fn test_round_trip() {
        fn round_trip(op: &BratOp) -> BratOp {
            println!("{}", op.name());
            BratOp::from_extension_op(
                &ExtensionOp::new(
                    EXTENSION.get_op(&op.name()).unwrap().clone(),
                    op.type_args(),
                    &BRAT_OPS_REGISTRY,
                )
                .unwrap(),
            )
            .unwrap()
        }

        let exts = ExtensionSet::from_iter([EXTENSION_ID]);
        let sig1 = Signature::new(vec![Type::UNIT, Type::UNIT], vec![Type::UNIT]);
        let sig2 = Signature::new(vec![Type::UNIT], vec![Type::UNIT, Type::UNIT]);
        let sig3 = Signature::new_endo(vec![Type::UNIT]);

        let hole = BratOp::Hole {
            idx: 0,
            sig: sig1.clone().with_extension_delta(exts.clone()),
        };
        assert_eq!(round_trip(&hole), hole);

        let substitute = BratOp::Substitute {
            func_sig: sig1.clone(),
            hole_sigs: vec![sig1.clone(), sig2.clone(), sig3.clone()],
        };
        assert_eq!(round_trip(&substitute), substitute);

        let make_closure = BratOp::MakeClosure { sig: sig1.clone() };
        assert_eq!(round_trip(&make_closure), make_closure);

        let closure_call = BratOp::ClosureCall { sig: sig1.clone() };
        assert_eq!(round_trip(&closure_call), closure_call);

        let partial = BratOp::Partial {
            inputs: vec![Type::UNIT].into(),
            output_sig: sig1.clone(),
        };
        assert_eq!(round_trip(&partial), partial);

        let panic = BratOp::Panic {
            sig: sig1.clone().with_extension_delta(exts.clone()),
        };
        assert_eq!(round_trip(&panic), panic);

        for ctor in all::<BratCtor>() {
            // Make dummy args for constructor params
            let args: Vec<TypeArg> = ctor
                .signature()
                .params()
                .iter()
                .map(|p| match p {
                    TypeParam::Type { .. } => TypeArg::Type { ty: Type::UNIT },
                    _ => panic!("Unexpected ctor parameter"),
                })
                .collect();

            let ctor_op = BratOp::Ctor {
                ctor,
                args: args.clone(),
            };
            assert_eq!(round_trip(&ctor_op), ctor_op);

            let prim_test = BratOp::PrimCtorTest { ctor, args };
            assert_eq!(round_trip(&prim_test), prim_test);
        }
    }
}
