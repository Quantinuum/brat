use anyhow;
use brat_extension;
use hugr::extension::{ExtensionRegistry, PRELUDE};
use hugr::std_extensions::arithmetic::{float_ops, float_types, int_ops, int_types};
use hugr::std_extensions::{collections, logic};
use hugr::{Hugr, HugrView};
use std::io::{stdin, Read};
use std::process::exit;

fn parse_and_validate() -> Result<(), anyhow::Error> {
    let mut buffer = String::new();
    let mut stdin = stdin();

    let registry = ExtensionRegistry::new([
        PRELUDE.to_owned(),
        logic::EXTENSION.to_owned(),
        int_types::EXTENSION.to_owned(),
        int_ops::EXTENSION.to_owned(),
        float_types::EXTENSION.to_owned(),
        float_ops::EXTENSION.to_owned(),
        collections::list::EXTENSION.to_owned(),
        brat_extension::EXTENSION.to_owned(),
    ]);

    stdin.read_to_string(&mut buffer).unwrap();
    let hugr = Hugr::load_str(&buffer, Some(&registry))?;
    hugr.validate()?;
    println!("hugr parsed & validated successfully!");
    Ok(())
}

fn main() {
    match parse_and_validate() {
        Ok(()) => (),
        Err(err) => {
            println!("{}", err);
            exit(1);
        }
    }
}
