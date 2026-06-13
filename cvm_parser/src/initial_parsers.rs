use cfg_ssa::ast::ComponentCreationMode;
use num_bigint::BigInt;
use nom::{
    branch::alt,
    bytes::tag,
    character::complete::{digit1, space1, usize, line_ending, not_line_ending},
    combinator::{map, value},
    multi::{separated_list1, count},
    sequence::{preceded, terminated},
    IResult, Parser,
};

use crate::parse_variable_name;

pub fn parse_prime(input: &str) -> IResult<&str, BigInt> {
    map(preceded(tag("%%prime"), preceded(space1, digit1)), |prime: &str| {
        BigInt::parse_bytes(prime.as_bytes(), 10).unwrap()
    })
    .parse(input)
}

pub fn parse_component_mode(input: &str) -> IResult<&str, ComponentCreationMode> {
    alt((
        value(ComponentCreationMode::Implicit, tag("implicit")),
        value(ComponentCreationMode::Explicit, tag("explicit")),
    ))
    .parse(input)
}

pub fn parse_signal_memory(input: &str) -> IResult<&str, usize> {
    map(preceded(tag("%%signals"), preceded(space1, usize)), |signals: usize| signals).parse(input)
}

pub fn parse_components_heap(input: &str) -> IResult<&str, usize> {
    map(preceded(tag("%%components_heap"), preceded(space1, usize)), |components_heap: usize| {
        components_heap
    })
    .parse(input)
}

pub fn parse_start(input: &str) -> IResult<&str, String> {
    map(preceded(tag("%%start"), preceded(space1,
                parse_variable_name)), |start: String| start)
        .parse(input)
}

pub fn parse_components(input: &str) -> IResult<&str, ComponentCreationMode> {
    map(
        preceded(tag("%%components"), preceded(space1, parse_component_mode)),
        |mode: ComponentCreationMode| mode,
    )
    .parse(input)
}

pub fn parse_witness(input: &str) -> IResult<&str, Vec<usize>> {
    map(
        preceded(tag("%%witness"), preceded(space1, separated_list1(space1, usize))),
        |witness: Vec<usize>| witness,
    )
    .parse(input)
}

pub fn parse_inputs(input: &str) -> IResult<&str, Vec<String>> {
    let (input, _) = tag("%%input").parse(input)?;
    let (input, _) = space1(input)?;
    let (input, num_inputs) = usize(input)?;
    let (input, _) = line_ending(input)?;

    let (input, lines) = count(
        terminated(map(not_line_ending, |s: &str| s.to_string()), line_ending),
        num_inputs,
    ).parse(input)?;

    Ok((input, lines))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_prime() {
        let input = "%%prime 123456789";
        let result = parse_prime(input);
        assert!(result.is_ok());
        let (remaining, prime) = result.unwrap();
        assert_eq!(remaining, "");
        assert_eq!(prime, BigInt::parse_bytes(b"123456789", 10).unwrap());
    }

    #[test]
    fn test_parse_component_mode() {
        let input = "implicit";
        let result = parse_component_mode(input);
        assert!(result.is_ok());
        let (remaining, mode) = result.unwrap();
        assert_eq!(remaining, "");
        assert_eq!(mode, ComponentCreationMode::Implicit);

        let input = "explicit";
        let result = parse_component_mode(input);
        assert!(result.is_ok());
        let (remaining, mode) = result.unwrap();
        assert_eq!(remaining, "");
        assert_eq!(mode, ComponentCreationMode::Explicit);
    }

    #[test]
    fn test_parse_signal_memory() {
        let input = "%%signals 1024";
        let result = parse_signal_memory(input);
        assert!(result.is_ok());
        let (remaining, signals) = result.unwrap();
        assert_eq!(remaining, "");
        assert_eq!(signals, 1024);
    }

    #[test]
    fn test_parse_components_heap() {
        let input = "%%components_heap 2048";
        let result = parse_components_heap(input);
        assert!(result.is_ok());
        let (remaining, components_heap) = result.unwrap();
        assert_eq!(remaining, "");
        assert_eq!(components_heap, 2048);
    }

    #[test]
    fn test_parse_start() {
        let input = "%%start main";
        let result = parse_start(input);
        println!("{:?}", result);
        assert!(result.is_ok());
        let (remaining, start) = result.unwrap();
        assert_eq!(remaining, "");
        assert_eq!(start, "main".to_string());
    }

    #[test]
    fn test_parse_components() {
        let input = "%%components implicit";
        let result = parse_components(input);
        assert!(result.is_ok());
        let (remaining, mode) = result.unwrap();
        assert_eq!(remaining, "");
        assert_eq!(mode, ComponentCreationMode::Implicit);

        let input = "%%components explicit";
        let result = parse_components(input);
        assert!(result.is_ok());
        let (remaining, mode) = result.unwrap();
        assert_eq!(remaining, "");
        assert_eq!(mode, ComponentCreationMode::Explicit);
    }

    #[test]
    fn test_parse_witness() {
        let input = "%%witness 1 2 3 4 53";
        let result = parse_witness(input);
        assert!(result.is_ok());
        let (remaining, witness) = result.unwrap();
        assert_eq!(remaining, "");
        assert_eq!(witness, vec![1, 2, 3, 4, 53]);
    }
}
