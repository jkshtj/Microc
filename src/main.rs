#[macro_use]
extern crate lalrpop_util;

mod symbol_table;
mod ast;

use crate::symbol_table::SYMBOL_TABLE;

use std::error::Error;
use std::fs::File;
use std::io::{BufReader, ErrorKind, Read};
use std::io;
use flexi_logger::Logger;

lalrpop_mod!(pub microc);

// TODO: Better error handling in general. Look here - https://doc.rust-lang.org/book/ch12-06-writing-to-stderr-instead-of-stdout.html
fn main() {
    fn inner_main() -> Result<(), Box<dyn Error>> {
        // Init logger
        Logger::try_with_env_or_str("Trace")?.start()?;

        let args = std::env::args().collect::<Vec<String>>();
        assert_eq!(args.len(), 3, "Must provide the input and output filenames!");
        let input_file_name = args.get(1).ok_or(io::Error::from(ErrorKind::InvalidInput))?;
        let result_file_name = args.get(2).ok_or(io::Error::from(ErrorKind::InvalidInput))?;

        let mut input_file = BufReader::new(File::open(input_file_name)?);
        let mut buf = String::new();
        input_file.read_to_string(&mut buf)?;

        let mut result_file = BufReader::new(File::open(result_file_name)?);
        let mut result = String::new();
        result_file.read_to_string(&mut result)?;

        println!("Beginning parsing file: [{}]", input_file_name);
        let program = microc::ProgramParser::new()
            .parse(&buf);

        /* STAGE2 result verification */
        // let result = result.trim();
        // if program.is_ok() && result == "Accepted" ||
        //     program.is_err() && result == "Not accepted" {
        //     println!("SUCCESS");
        // } else {
        //     println!("FAILURE");
        // }
        /*******************************/

        /* STAGE3 result verification */
        let symbol_table = SYMBOL_TABLE.borrow();
        let mut actual_result = format!("{}", &*symbol_table);
        actual_result.retain(|x| !x.is_whitespace());
        result.retain(|x| !x.is_whitespace());

        // println!("Actual result:\n {}", actual_result);
        // println!();
        // println!("Expected result:\n {}", result);

        assert_eq!(actual_result, result);
        println!("SUCCESS");

        /*******************************/

        Ok(())
    }

    if let Err(e) = inner_main() {
        eprintln!("Unable to complete parsing input: {}", e);
        std::process::exit(1);
    }
}