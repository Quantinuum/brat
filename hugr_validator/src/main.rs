use brat_extension;
use clap::Parser;
use clio::Input;
use hugr::extension::{ExtensionRegistry, PRELUDE};
use hugr::std_extensions::arithmetic::{float_ops, float_types, int_ops, int_types};
use hugr::std_extensions::{collections, logic};
use hugr::HugrView;
use hugr::{hugr::ValidationError, Hugr};
use serde_json;
use std::io::{stdin, stdout, Read, Write};
use std::process::exit;

#[derive(Parser, Debug)]
#[command(version, about)]
pub struct CliArgs {
    #[arg(default_value = "-", help = "Input hugr")]
    input_file: Input,

    // Vizualise the hugr instead of validating it
    #[arg(long, default_value_t = false)]
    viz: bool,
}

fn parse_hugr(contents: impl std::io::Read) -> Hugr {
    serde_json::from_reader(contents).expect("Couldn't parse hugr")
}

fn validate(hugr: &Hugr) -> Result<(), ValidationError> {
    let registry = ExtensionRegistry::try_new([
        PRELUDE.to_owned(),
        logic::EXTENSION.to_owned(),
        int_types::extension(),
        int_ops::EXTENSION.to_owned(),
        float_types::EXTENSION.to_owned(),
        float_ops::EXTENSION.to_owned(),
        collections::EXTENSION.to_owned(),
        brat_extension::EXTENSION.to_owned(),
    ])
    .unwrap();

    hugr.validate(&registry)?;
    println!("hugr parsed & validated successfully!");
    Ok(())
}

fn main() -> Result<(), ValidationError> {
    let args = CliArgs::parse();
    let hugr = parse_hugr(args.input_file);
    if args.viz {
        let mermaid = hugr.mermaid_string();
        println!("{mermaid}");
        Ok(())
    } else {
        match validate(&hugr) {
            Ok(()) => Ok(()),
            Err(err) => {
                println!("{}", err);
                exit(1);
            }
        }
    }
}
