#![feature(box_into_inner)]
#![allow(unused_imports)]
mod asm;
mod ast;
mod cfg;
mod register_alloc;
mod symbol_table;
mod three_addr_code_ir;
mod token;

#[macro_use]
extern crate lalrpop_util;

// use crate::asm::tiny::TinyCodeSequence;
use crate::cfg::basic_block::BBFunction;
use crate::symbol_table::{SymbolTable, SYMBOL_TABLE};
use crate::three_addr_code_ir::three_address_code::{
    visit::ThreeAddressCodeVisitor, ThreeAddressCode,
};

use crate::cfg::liveness::LivenessDecoratedControlFlowGraph;
use crate::cfg::ControlFlowGraph;
use flexi_logger::Logger;
use std::error::Error;
use std::fs::File;
use std::io;
use std::io::{BufReader, ErrorKind, Read};
use three_addr_code_ir::three_address_code::visit::CodeObject;
use crate::asm::tiny::TinyCodeSequence;

lalrpop_mod!(pub microc);

// TODO: Better error handling in general. Look here - https://doc.rust-lang.org/book/ch12-06-writing-to-stderr-instead-of-stdout.html
fn main() {
    fn inner_main() -> Result<(), Box<dyn Error>> {
        // Init logger
        Logger::try_with_env_or_str("Trace")?.start()?;

        let args = std::env::args().collect::<Vec<String>>();
        assert_eq!(
            args.len(),
            3,
            "Must provide the input and output filenames!"
        );
        let input_file_name = args
            .get(1)
            .ok_or(io::Error::from(ErrorKind::InvalidInput))?;
        let result_file_name = args
            .get(2)
            .ok_or(io::Error::from(ErrorKind::InvalidInput))?;

        let mut input_file = BufReader::new(File::open(input_file_name)?);
        let mut buf = String::new();
        input_file.read_to_string(&mut buf)?;

        let mut result_file = BufReader::new(File::open(result_file_name)?);
        let mut result = String::new();
        result_file.read_to_string(&mut result)?;

        println!("Beginning parsing file: [{}]", input_file_name);
        let program = microc::ProgramParser::new().parse(&buf);

        /* STAGE 2 result verification */
        // let result = result.trim();
        // if program.is_ok() && result == "Accepted" ||
        //     program.is_err() && result == "Not accepted" {
        //     println!("SUCCESS");
        // } else {
        //     println!("FAILURE");
        // }
        /*******************************/

        /* STAGE 3 result verification */
        // let symbol_table = SYMBOL_TABLE.borrow();
        // let mut actual_result = format!("{}", &*symbol_table);
        // actual_result.retain(|x| !x.is_whitespace());
        // result.retain(|x| !x.is_whitespace());
        //
        // // println!("Actual result:\n {}", actual_result);
        // // println!();
        // // println!("Expected result:\n {}", result);
        //
        // assert_eq!(actual_result, result);
        // println!("SUCCESS");

        /*******************************/

        /* STAGE 4,5,6 result verification */
        let mut result = program.unwrap();
        let mut visitor = ThreeAddressCodeVisitor;
        result.reverse();
        // let three_addr_codes: Vec<ThreeAddressCode> = result
        //     .into_iter()
        //     .flat_map(|ast_node| visitor.walk_ast(ast_node).code_sequence)
        //     .collect();
        //
        // three_addr_codes
        //     .clone()
        //     .into_iter()
        //     .for_each(|code| println!(";{}", code));

        // result
        //     .into_iter()
        //     .map(|ast_node| visitor.walk_ast(ast_node))
        //     .map(|code_object| Into::<BBFunction>::into(code_object))
        //     .for_each(|x| println!("{x}"));

        result
            .into_iter()
            .map(|ast_node| visitor.walk_ast(ast_node))
            .map(|code_object| ControlFlowGraph::from(Into::<BBFunction>::into(code_object)))
            .map(|cfg| LivenessDecoratedControlFlowGraph::from(cfg))
            .map(|cfg| register_alloc::perform_register_allocation(cfg, 4))
            .map(|register_alloc_tacs| Into::<TinyCodeSequence>::into(register_alloc_tacs))
            .for_each(|tiny_code_seq| tiny_code_seq
                .sequence
                .into_iter()
                .for_each(|code| println!("{code}"))
            );

        // let tiny_code: TinyCodeSequence = three_addr_codes.into();
        // tiny_code
        //     .sequence
        //     .into_iter()
        //     .for_each(|code| println!("{code}"));
        /*******************************/

        Ok(())
    }

    if let Err(e) = inner_main() {
        eprintln!("Unable to complete parsing input: {}", e);
        std::process::exit(1);
    }
}
