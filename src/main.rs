/*
 * Copyright 2018-2024 Felix Garcia Carballeira, Alejandro Calderon Mateos, Diego Camarmas Alonso,
 * Álvaro Guerrero Espinosa
 *
 * This file is part of CREATOR.
 *
 * CREATOR is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * CREATOR is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with CREATOR.  If not, see <http://www.gnu.org/licenses/>.
 */

use creator_compiler::{architecture::Architecture, compiler, parser, RenderError};

fn main() {
    let mut args = std::env::args();
    args.next();
    let operation = args
        .next()
        .expect("Expected operation code")
        .parse::<i32>()
        .expect("Expected operation code to be a number");
    if operation == 0 {
        println!("{}", Architecture::schema());
        return;
    }
    let filename = args.next().expect("Expected file argument");
    let arch = std::fs::read_to_string(filename).expect("We should be able to read the file");
    let arch = Architecture::from_json(&arch).expect("The input JSON should be correct");
    if operation == 1 {
        println!("{arch:#?}");
    } else {
        let filename = args.next().expect("Expected file argument");
        let src = std::fs::read_to_string(&filename).expect("We should be able to read the file");
        match parser::parse(&src) {
            Err(errors) => print!("{}", errors.render(&filename, &src)),
            Ok(ast) => {
                println!("{ast:#?}");
                if operation == 3 {
                    match compiler::compile(&arch, ast) {
                        Ok(compiled_code) => {
                            println!("{compiled_code:#?}");
                        }
                        Err(e) => print!("{}", e.render(&filename, &src)),
                    };
                }
            }
        }
    }
}
