extern crate num_bigint_dig as num_bigint;

use nom::{
    branch::alt,
    bytes::tag,
    character::{
        complete::{alphanumeric1, multispace1, none_of, satisfy, space0, usize,},
        streaming::space1,
    },
    combinator::{complete, cut, eof, map, opt, peek, recognize, value},
    multi::{count, many0, many_till, separated_list0},
    sequence::{
        delimited, pair, preceded,
    },
    IResult, Parser,
};
use cfg_ssa::{ast::*, types::NumericType};

mod initial_parsers;
mod operation_parsers;
use initial_parsers::*;
use num_bigint::BigInt;
use operation_parsers::{parse_expression, parse_operation, parse_numeric_type};

fn parse_variable_name(input: &str) -> IResult<&str, String> {
    recognize(
        pair(
            satisfy(|c| c.is_ascii_alphabetic() || c == '_'),
            many0(satisfy(|c| c.is_ascii_alphanumeric() || c == '_'))
        )
    ).parse(input)
    .map(|(remain, var)| (remain, var.to_string()))
}

fn parse_function_name(input: &str) -> IResult<&str, String> {
    preceded(
        satisfy(|c| c == '$'),
        recognize(many0(satisfy(|c| c.is_ascii_alphanumeric() || c == '_')))
    ).parse(input)
    .map(|(remain, var)| (remain, var.to_string()))
}

fn parse_comment(input: &str) -> IResult<&str, ()> {
    let (input, _) = preceded(tag(";;"), many0(none_of("\n"))).parse(input)?;
    Ok((input, ()))
}

fn parse_useless(input: &str) -> IResult<&str, ()> {
    let (input, _) = opt(many0(alt((
        map(multispace1, |_| ()),
        complete(parse_comment),
    ))
    )).parse(input)?;
    Ok((input, ()))
}

fn parse_loop_aux(input: &str) -> IResult<&str, ASTNode> {
    let (input, body) = many0(parse_ast_node).parse(input)?;
    let (input, _) = tag("end").parse(input)?;
    Ok((input, ASTNode::Loop {body}))
}

fn parse_loop(input: &str) -> IResult<&str, ASTNode> {
    preceded(tag("loop"), cut(parse_loop_aux)).parse(input)
}

fn parse_if_then_else_aux(input: &str, num_type: NumericType) -> IResult<&str, ASTNode> {
    let (input, _) = space1(input)?;
    let (input, condition) = parse_expression(input)?;
    let (input, if_case) = many0(parse_ast_node).parse(input)?;
    let (input, else_case) = opt(preceded(tag("else"), many0(parse_ast_node))).parse(input)?;
    let (input, _) = tag("end").parse(input)?;
    Ok((input, ASTNode::IfThenElse {num_type, condition, if_case, else_case}))
}

fn parse_if_then_else(input: &str) -> IResult<&str, ASTNode> {
    alt((
        preceded(tag("i64.if"),
        cut(|input| parse_if_then_else_aux(input, NumericType::Integer))),

        preceded(tag("ff.if"),
        cut(|input| parse_if_then_else_aux(input, NumericType::FiniteField))),
    ))
    .parse(input)
}

fn parse_break(input: &str) -> IResult<&str, ASTNode> {
    value(ASTNode::Break, tag("break")).parse(input)
}

fn parse_continue(input: &str) -> IResult<&str, ASTNode> {
    value(ASTNode::Continue, tag("continue")).parse(input)
}

fn parse_ast_node(input: &str) -> IResult<&str, ASTNode> {
    //Delimited by useless to avoid parsing comments and whitespaces
    complete(delimited(
            parse_useless,
            alt((
                    parse_if_then_else,
                    parse_loop,
                    parse_break,
                    parse_continue,
                    parse_operation)),
            parse_useless
    )).parse(input)
}

fn parse_id_name(input: &str) -> Result<usize, nom::Err<nom::error::Error<&str>>> {
    let (input, _) = many0(complete(preceded(alphanumeric1, tag("_")))).parse(input)?;
    let (_, id) = usize(input)?;
    Ok(id)
}

fn parse_function_input(input: &str) -> IResult<&str, (NumericType, Vec<usize>)> {
    let (input, (in_type, _, n)) = (parse_numeric_type, space1, usize).parse(input)?;
    let (input, dims) = count(
        preceded(space1, usize),
        n,
    ).parse(input)?;

    Ok((input, (in_type, dims)))
}

fn parse_function_inputs(input: &str) -> IResult<&str, Vec<(NumericType, Vec<usize>)>> {
    separated_list0(space1, parse_function_input).parse(input)
}

fn parse_function(input: &str) -> IResult<&str, Function> {
    let (input, _) = tag("%%function").parse(input)?;
    let (input, _) = space1(input)?;

    let (input, name) = parse_variable_name(input)?;
    let (input, _) = space0(input)?;

    let id = parse_id_name(&name);
    let id = match id {
        Ok(id) => id,
        Err(_) => return Err(nom::Err::Failure(nom::error::Error::new(input, nom::error::ErrorKind::Fail))),
    };

    //Parse output type
    let (input, output) = delimited(
        (tag("["), space0),
            alt((
                map(parse_numeric_type, Some),
                value(None, tag("")),
            )),
        (space0, tag("]"))
    ).parse(input)?;
    
    let (input, _) = space0(input)?;

    //Parse inputs types
    let (input, inputs) = delimited(
        (tag("["), space0),
    parse_function_inputs, 
    (space0, tag("]")),
    ).parse(input)?;
    let (input, _) = parse_useless(input)?;

    let (input, (body, _)) = many_till(parse_ast_node, alt((peek(eof), peek(tag("%%"))))).parse(input)?;

    Ok((input, Function {
        id,
        name,
        output,
        inputs,
        body,
    }))
}

fn parse_template(input: &str) -> IResult<&str, Template> {
    let (input, _) = tag("%%template").parse(input)?;
    let (input, _) = space1(input)?;

    let (input, name) = parse_variable_name(input)?;
    let (input, _) = space0(input)?;

    let id = parse_id_name(&name);
    let id = match id {
        Ok(id) => id,
        Err(_) => return Err(nom::Err::Failure(nom::error::Error::new(input, nom::error::ErrorKind::Fail))),
    };

    let (input, outputs) = delimited(tag("["),
    delimited(space0, separated_list0(space1, alphanumeric1), space0), 
    tag("]")).parse(input)?;
    let outputs = outputs.iter().map(|x| x.to_string()).collect();
    let (input, _) = space0(input)?;

    let (input, inputs) = delimited(tag("["),
    delimited(space0, separated_list0(space1, alphanumeric1), space0), 
    tag("]")).parse(input)?;
    let inputs = inputs.iter().map(|x| x.to_string()).collect();
    let (input, _) = space0(input)?;

    let (input, signals) = delimited(tag("["),
    delimited(space0, usize, space0),
    tag("]")).parse(input)?;
    let (input, _) = space0(input)?;

    let (input, components) = delimited(tag("["),
    delimited(space0, separated_list0(space1, usize), space0),
    tag("]")).parse(input)?;

    let (input, (body, _)) = many_till(parse_ast_node, alt((peek(eof), peek(tag("%%"))))).parse(input)?;

    Ok((input, Template {
        id,
        name,
        outputs,
        inputs,
        signals,
        components,
        body,
    }))
}

#[derive(Debug)]
enum ASTField {
    Field(BigInt),
    SignalsMemory(usize),
    ComponentsHeap(usize),
    MainTemplate(String),
    ComponentsCreationMode(ComponentCreationMode),
    Witness(Vec<usize>),
    Inputs(Vec<String>),
    Template(Template),
    Function(Function),
}

fn parse_ast_field(input: &str) -> IResult<&str, ASTField> {
    complete(preceded(parse_useless, alt((
            map(parse_prime, ASTField::Field),
            map(parse_signal_memory, ASTField::SignalsMemory),
            map(parse_components_heap, ASTField::ComponentsHeap),
            map(parse_start, ASTField::MainTemplate),
            map(parse_components, ASTField::ComponentsCreationMode),
            map(parse_witness, ASTField::Witness),
            map(parse_inputs, ASTField::Inputs),
            map(parse_function, ASTField::Function),
            map(parse_template, ASTField::Template),
    )))).parse(input)
}

pub fn parse_program(input: &str) -> IResult<&str, AST> {
    let (remaining_input, (fields, _)) = many_till(parse_ast_field, eof).parse(input)?;

    // Temporary storage for each field
    let mut field_opt: Option<BigInt> = None;
    let mut signals_memory_opt: Option<usize> = None;
    let mut components_heap_opt: Option<usize> = None;
    let mut main_template_opt: Option<String> = None;
    let mut components_creation_mode_opt: Option<ComponentCreationMode> = None;
    let mut witness: Option<Vec<usize>> = None;
    let mut inputs_opt: Option<Vec<String>> = None;
    let mut templates: Vec<Template> = Vec::new();
    let mut functions: Vec<Function> = Vec::new();

    // Process each parsed field
    // If one is repeated -> TODO: Error (current) or change value?
    for ast_field in fields {
        match ast_field {
            ASTField::Field(val) => {
                if field_opt.is_some() {
                    return Err(nom::Err::Failure(nom::error::Error::new(input, nom::error::ErrorKind::Fail)));
                }
                field_opt = Some(val);
            }
            ASTField::SignalsMemory(val) => {
                if signals_memory_opt.is_some() {
                    return Err(nom::Err::Failure(nom::error::Error::new(input, nom::error::ErrorKind::Fail)));
                }
                signals_memory_opt = Some(val);
            }
            ASTField::ComponentsHeap(val) => {
                if components_heap_opt.is_some() {
                    return Err(nom::Err::Failure(nom::error::Error::new(input, nom::error::ErrorKind::Fail)));
                }
                components_heap_opt = Some(val);
            }
            ASTField::MainTemplate(val) => {
                if main_template_opt.is_some() {
                    return Err(nom::Err::Failure(nom::error::Error::new(input, nom::error::ErrorKind::Fail)));
                }
                main_template_opt = Some(val);
            }
            ASTField::ComponentsCreationMode(val) => {
                if components_creation_mode_opt.is_some() {
                    return Err(nom::Err::Failure(nom::error::Error::new(input, nom::error::ErrorKind::Fail)));
                }
                components_creation_mode_opt = Some(val);
            }
            ASTField::Witness(vec) => {
                if witness.is_some() {
                    return Err(nom::Err::Failure(nom::error::Error::new(input, nom::error::ErrorKind::Fail)));
                }
                witness = Some(vec);
            }
            ASTField::Inputs(vec) => {
                if inputs_opt.is_some() {
                    return Err(nom::Err::Failure(nom::error::Error::new(input, nom::error::ErrorKind::Fail)));
                }
                inputs_opt = Some(vec);
            }
            ASTField::Template(tem) => {
                templates.push(tem);
            }
            ASTField::Function(fun) => {
                functions.push(fun);
            }
        }
    }

    // Check that all required fields were found.
    let field = field_opt.ok_or(nom::Err::Failure(nom::error::Error::new(input, nom::error::ErrorKind::Fail)))?;
    let signals_memory = signals_memory_opt.ok_or(nom::Err::Failure(nom::error::Error::new(input, nom::error::ErrorKind::Fail)))?;
    let components_heap = components_heap_opt.ok_or(nom::Err::Failure(nom::error::Error::new(input, nom::error::ErrorKind::Fail)))?;
    let main_template = main_template_opt.ok_or(nom::Err::Failure(nom::error::Error::new(input, nom::error::ErrorKind::Fail)))?;
    let components_creation_mode = components_creation_mode_opt.ok_or(nom::Err::Failure(nom::error::Error::new(input, nom::error::ErrorKind::Fail)))?;
    let witness = witness.ok_or(nom::Err::Failure(nom::error::Error::new(input, nom::error::ErrorKind::Fail)))?;

    Ok((
        remaining_input,
        AST {
            field,
            signals_memory,
            components_heap,
            main_template,
            components_creation_mode,
            witness,
            inputs: inputs_opt,
            functions,
            templates,
        },
    ))
}

#[cfg(test)]
mod tests {
    use cfg_ssa::types::{Atomic, ConstantType, Expression, NumericType, Operator};

    use super::*;

    #[test]
    fn test_parse_variable_name() {
        assert_eq!(parse_variable_name("_var1"), Ok(("", "_var1".to_string())));
        assert_eq!(parse_variable_name("var3"), Ok(("", "var3".to_string())));
        assert_eq!(parse_variable_name("var"), Ok(("", "var".to_string())));
        assert!(parse_variable_name("1var").is_err());
    }

    #[test]
    fn test_parse_function_name() {
        assert_eq!(parse_function_name("$func1"), Ok(("", "func1".to_string())));
        assert!(parse_function_name("1func").is_err());
        assert!(parse_function_name("func").is_err());
    }

    #[test]
    fn test_parse_comment() {
        assert_eq!(parse_comment(";; this is a comment\n"), Ok(("\n", ())));
        assert!(parse_comment("this is not a comment").is_err());
    }

    #[test]
    fn test_parse_useless() {
        assert_eq!(parse_useless("   ;; comment\n  ;;lkasjfl\n "), Ok(("", ())));
        assert_eq!(parse_useless("   \n   "), Ok(("", ())));
        assert!(parse_useless("").is_ok());
    }

    #[test]
    fn test_parse_loop() {
        let input = "loop\n  ;; comment\n  x = ff.add x y\n y = i64.sub i64.3 z\n ;;comment\n end\n";
        assert_eq!(parse_loop(input), Ok(("\n", ASTNode::Loop { body: vec![
            ASTNode::Operation {
            num_type: Some(NumericType::FiniteField),
            operator: Some(Operator::Add),
            output: Some("x".to_string()),
            operands: vec![
                Expression::Atomic(Atomic::Variable("x".to_string())),
                Expression::Atomic(Atomic::Variable("y".to_string()))
            ],
            },
            ASTNode::Operation {
            num_type: Some(NumericType::Integer),
            operator: Some(Operator::Sub),
            output: Some("y".to_string()),
            operands: vec![
                Expression::Atomic(Atomic::Constant(ConstantType::I64(3))),
                Expression::Atomic(Atomic::Variable("z".to_string()))
            ],
            }
        ]})));
    }

    #[test]
    fn test_parse_if_then_else() {
        let input = "ff.if condition\n  ;; comment\n x = ff.add x y\n else\n  ;; comment\n x = ff.1 end\n";
        let expected = ASTNode::IfThenElse {
            num_type: NumericType::FiniteField,
            condition: Expression::Atomic(Atomic::Variable("condition".to_string())),
            if_case: vec![ASTNode::Operation {
                num_type: Some(NumericType::FiniteField),
                operator: Some(Operator::Add),
                output: Some("x".to_string()),
                operands: vec![Expression::Atomic(Atomic::Variable("x".to_string())), Expression::Atomic(Atomic::Variable("y".to_string()))],
            }],
            else_case: Some(vec![ASTNode::Operation {
                num_type: None,
                operator: None,
                output: Some("x".to_string()),
                operands: vec![Expression::Atomic(Atomic::Constant(ConstantType::FF(BigInt::from(1))))],
            }]),
        };
        assert_eq!(parse_if_then_else(input), Ok(("\n", expected)));
    }

    #[test]
    fn test_parse_if_no_else() {
        let input = "i64.if condition\n  x = ff.add x y\n end\n";
        let expected = ASTNode::IfThenElse {
            num_type: NumericType::Integer,
            condition: Expression::Atomic(Atomic::Variable("condition".to_string())),
            if_case: vec![ASTNode::Operation {
                num_type: Some(NumericType::FiniteField),
                operator: Some(Operator::Add),
                output: Some("x".to_string()),
                operands: vec![
                    Expression::Atomic(Atomic::Variable("x".to_string())),
                    Expression::Atomic(Atomic::Variable("y".to_string())),
                ],
            }],
            else_case: None,
        };
        assert_eq!(parse_if_then_else(input), Ok(("\n", expected)));
    }

    #[test]
    fn test_parse_function() {
        let input = "%%function my_function_0 [ff] [ff 1 1 i64 0]\n\n  ;; body\n x = ff.add y z\n\n";
        let expected = Function {
            id: 0,
            name: "my_function_0".to_string(),
            output: Some(NumericType::FiniteField),
            inputs: vec![
                (NumericType::FiniteField, vec![1]),
                (NumericType::Integer, vec![]),
            ],
            body: vec![ASTNode::Operation {
                num_type: Some(NumericType::FiniteField),
                operator: Some(Operator::Add),
                output: Some("x".to_string()),
                operands: vec![
                    Expression::Atomic(Atomic::Variable("y".to_string())),
                    Expression::Atomic(Atomic::Variable("z".to_string())),
                ],
            }],
        };
        assert_eq!(parse_function(input), Ok(("", expected)));
    }

    #[test]
    fn test_parse_function2() {
        let input = "%%function POSEIDON_C_0 [] [ i64 0 i64 0 ff 0 ]\n\n  ;; body\n x = ff.add y z\n\n";
        let expected = Function {
            id: 0,
            name: "POSEIDON_C_0".to_string(),
            output: None,
            inputs: vec![
                (NumericType::Integer, vec![]),
                (NumericType::Integer, vec![]),
                (NumericType::FiniteField, vec![]),
            ],
            body: vec![ASTNode::Operation {
                num_type: Some(NumericType::FiniteField),
                operator: Some(Operator::Add),
                output: Some("x".to_string()),
                operands: vec![
                    Expression::Atomic(Atomic::Variable("y".to_string())),
                    Expression::Atomic(Atomic::Variable("z".to_string())),
                ],
            }],
        };
        assert_eq!(parse_function(input), Ok(("", expected)));
    }

    #[test]
    fn test_error_ast_node() {
        let input = "error 0";
        println!("{:?}", parse_ast_node(input));
        assert!(parse_ast_node(input).is_err());
    }

    #[test]
    fn test_parse_id_template() {
        let input = "template_20";
        assert_eq!(parse_id_name(input), Ok(20));
    }

    #[test]
    fn test_parse_id_template_2() {
        let input = "template_alfa_23_20";
        assert_eq!(parse_id_name(input), Ok(20));
    }

    #[test]
    fn test_parse_template() {
        let input = "%%template template_0 [output] [input1 input2] [10] [5 3 2]\n  ;; body\n x = ff.add y z\n ;;Me jodes?\n loop\n ;;Y tu?\n y = ff.mul x z\n end\n ff.if condition\n  z = ff.sub x y\n else\n  z = ff.div x y\n end\n";
        let res = parse_template(input);
        println!("{:?}", res);
        assert_eq!(res, Ok(("", Template {
            id: 0,
            name: "template_0".to_string(),
            outputs: vec!["output".to_string()],
            inputs: vec!["input1".to_string(), "input2".to_string()],
            signals: 10,
            components: vec![5, 3, 2],
            body: vec![
            ASTNode::Operation {
                num_type: Some(NumericType::FiniteField),
                operator: Some(Operator::Add),
                output: Some("x".to_string()),
                operands: vec![
                Expression::Atomic(Atomic::Variable("y".to_string())),
                Expression::Atomic(Atomic::Variable("z".to_string())),
                ],
            },
            ASTNode::Loop {
                body: vec![
                ASTNode::Operation {
                    num_type: Some(NumericType::FiniteField),
                    operator: Some(Operator::Mul),
                    output: Some("y".to_string()),
                    operands: vec![
                    Expression::Atomic(Atomic::Variable("x".to_string())),
                    Expression::Atomic(Atomic::Variable("z".to_string())),
                    ],
                },
                ],
            },
            ASTNode::IfThenElse {
                num_type: NumericType::FiniteField,
                condition: Expression::Atomic(Atomic::Variable("condition".to_string())),
                if_case: vec![
                ASTNode::Operation {
                    num_type: Some(NumericType::FiniteField),
                    operator: Some(Operator::Sub),
                    output: Some("z".to_string()),
                    operands: vec![
                    Expression::Atomic(Atomic::Variable("x".to_string())),
                    Expression::Atomic(Atomic::Variable("y".to_string())),
                    ],
                },
                ],
                else_case: Some(vec![
                ASTNode::Operation {
                    num_type: Some(NumericType::FiniteField),
                    operator: Some(Operator::Div),
                    output: Some("z".to_string()),
                    operands: vec![
                    Expression::Atomic(Atomic::Variable("x".to_string())),
                    Expression::Atomic(Atomic::Variable("y".to_string())),
                    ],
                },
                ]),
            },
            ],
        })));
    }

    #[test]
    fn test_parse_template_error() {
        let input = "%%template template_0 [output] [input1 input2] [10] [5 3 2]\n  ;; body\n loop\n x1 = ff.add i64.0 i64.2 \n error 0\n end\n \n";
        let res = parse_template(input);
        println!("{:?}", res);
        assert!(res.is_err());
    }

    #[test]
    fn test_parse_if2() {
        let input = "loop\n x1 = i64.0 \n error 0\nend";
        let res = parse_loop(input);
        println!("{:?}", res);
        assert!(res.is_err());
    }

    //TODO: What to do with these tests?
    // #[test]
    // fn test_parse_program() {
    //     let input = fs::read_to_string("test/test_program.cvm").unwrap();
    //     let res = parse_program(&input);
    //     let mut file = fs::File::create("test/output.txt").unwrap();
    //     writeln!(file, "{:?}", res).unwrap();
    //     assert!(res.is_ok());
    // }


    // #[test]
    // fn test_parse_compiled_files() {
    //     let compiled_folder = Path::new("./test/compiled/");
    
    //     // Process a single file: read, parse, and type check.
    //     fn process_file(path: &Path) -> bool {
    //         let content = match fs::read_to_string(path) {
    //             Ok(content) => content,
    //             Err(e) => {
    //                 eprintln!("Failed to read file {:?}: {:?}", path, e);
    //                 return false;
    //             }
    //         };
    
    //         match parse_program(&content) {
    //             Ok(("", parsed)) => {
    //                 println!("Parsed successfully: {:?}", path);
    //                 let output_path = Path::new("./test/outputs/successes/").join(path.file_name().unwrap());
    //                 let mut output_file = fs::File::create(output_path).unwrap();
    //                 writeln!(output_file, "{:?}", parsed).unwrap();
    //                 true
    //             }
    //             Ok((remaining, _)) => {
    //                 eprintln!("Parsing failed for file {:?}", path);
    //                 let error_file_name = format!("./test/outputs/fails/{}_error.txt", path.file_name().unwrap().to_string_lossy());
    //                 let mut error_file = fs::File::create(error_file_name).unwrap();
    //                 writeln!(error_file, "Parsing failed for file {:?}: remaining input:\n {:?}", path, remaining).unwrap();
    //                 false
    //             }
    //             Err(e) => {
    //                 eprintln!("Parsing failed for file {:?}", path);
    //                 let error_file_name = format!("./test/outputs/fails/{}_error.txt", path.file_name().unwrap().to_string_lossy());
    //                 let mut error_file = fs::File::create(error_file_name).unwrap();
    //                 writeln!(error_file, "Parsing failed for file {:?}:\n {:?}", path, e).unwrap();
    //                 false
    //             }
    //         }
    //     }
    
    //     // Recursively process all files in the directory.
    //     fn process_directory(dir: &Path) -> bool {
    //         let mut res = true;
    //         for entry in fs::read_dir(dir).unwrap_or_else(|e| {
    //             panic!("Failed to read directory {:?}: {:?}", dir, e);
    //         }) {
    //             let entry = entry.expect("Failed to read directory entry");
    //             let path = entry.path();
    //             if path.is_dir() {
    //                 process_directory(&path);
    //             } else if path.is_file() {
    //                 if let false = process_file(&path) {
    //                     res = false;
    //                 }
    //             }
    //         }

    //         res
    //     }
    
    //     assert!(process_directory(compiled_folder));
    // }
}
