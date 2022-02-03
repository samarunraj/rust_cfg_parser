//! A very simple Rust library to parse rust cfg() expression.
//!
//! # Examples
//!
//! ``` rust
//! use rust_cfg_parser::{parse, CfgValue};
//!
//! let expr = parse("cfg(windows)").unwrap();
//!
//! let matches = expr.matches(&[CfgValue::Name("linux".to_string())]);
//! assert_eq!(false, matches);
//!
//! let matches = expr.matches(&[CfgValue::Name("windows".to_string())]);
//! assert_eq!(true, matches);
//!
//! let expr = parse(
//!     "cfg(all(any(target_arch =\"x86_64\", target_arch = \"aarch64\"), target_os = \"hermit\"))",
//! )
//! .unwrap();
//! assert_eq!(
//!     true,
//!     expr.matches(&[
//!         CfgValue::KeyPair("target_arch".to_string(), "x86_64".to_string()),
//!         CfgValue::KeyPair("target_os".to_string(), "hermit".to_string())
//!     ])
//! );
//! ```
#![cfg_attr(not(feature = "std"), no_std)]
use cfg_if::cfg_if;
use std::fmt;
use std::fmt::{Display, Formatter};

cfg_if! {
    if #[cfg(not(feature = "std"))] {
        extern crate alloc;

        use alloc::boxed::Box;
        use alloc::string::String;
        use alloc::vec::Vec;
    }
}

#[doc(hidden)]
struct CommaSeparated<'a, T>(&'a [T]);

impl<'a, T: fmt::Display> fmt::Display for CommaSeparated<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for (i, v) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", {}", v)?;
            } else {
                write!(f, "{}", v)?;
            }
        }
        Ok(())
    }
}

/// Defines the parser error type.
#[derive(Debug)]
pub struct CfgParseError {
    #[allow(dead_code)]
    kind: CfgParseErrorKind,
}

impl CfgParseError {
    fn new(kind: CfgParseErrorKind) -> CfgParseError {
        CfgParseError { kind }
    }
}

impl Display for CfgParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.kind)
    }
}

impl std::error::Error for CfgParseError {}

/// An enum type for errors when parsing the cfg string.
#[derive(Debug, PartialEq)]
#[non_exhaustive]
pub enum CfgParseErrorKind {
    ExpectedLeftParentheses,
    ExpectedString,
    IncompatibleString,
    OutOfBounds,
    UnBalancedParentheses,
    UnExpectedString,
}

/// An enum type to represent the parsed values in a cfg string.
#[derive(Eq, PartialEq, Hash, Ord, PartialOrd, Clone, Debug)]
pub enum CfgValue {
    /// A configuration value as name/value pair.
    KeyPair(String, String),
    /// A configuration value.
    Name(String),
}

/// An enum type to represent the parsed cfg string.
#[derive(Eq, PartialEq, Hash, Ord, PartialOrd, Clone, Debug)]
pub enum CfgExpr {
    /// An expression that is true when all of the sub-expressions are true.
    All(Vec<CfgExpr>),
    /// An expression that is true when any of the sub-expressions are true.
    Any(Vec<CfgExpr>),
    /// An expression that applies the not operator to the sub-expressions.
    Not(Box<CfgExpr>),
    /// An expression that can be a name or name/value pair.
    Value(CfgValue),
}

impl CfgExpr {
    fn matches(&self, cfg: &[CfgValue]) -> bool {
        match self {
            CfgExpr::All(e) => e.iter().all(|e| e.matches(cfg)),
            CfgExpr::Any(e) => e.iter().any(|e| e.matches(cfg)),
            CfgExpr::Not(e) => !e.matches(cfg),
            CfgExpr::Value(e) => cfg.contains(e),
        }
    }
}

impl fmt::Display for CfgExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CfgExpr::All(t) => write!(f, "all({})", CommaSeparated(t)),
            CfgExpr::Any(t) => write!(f, "any({})", CommaSeparated(t)),
            CfgExpr::Not(t) => write!(f, "not({})", t),
            CfgExpr::Value(v) => match v {
                CfgValue::KeyPair(k, v) => write!(f, "{} = \"{}\"", k, v),
                CfgValue::Name(t) => write!(f, "{}", t),
            },
        }
    }
}

#[doc(hidden)]
#[derive(PartialEq)]
enum CfgToken<'a> {
    Comma,
    Equals,
    Ident(&'a str),
    LeftParen,
    RightParen,
    Space,
    String(&'a str),
    Unknown,
}

impl<'a> fmt::Display for CfgToken<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CfgToken::Comma => write!(f, ","),
            CfgToken::Equals => write!(f, "="),
            CfgToken::Ident(t) => write!(f, "{}", t),
            CfgToken::LeftParen => write!(f, "("),
            CfgToken::RightParen => write!(f, ")"),
            CfgToken::Space => write!(f, " "),
            CfgToken::String(t) => write!(f, "{}", t),
            CfgToken::Unknown => write!(f, "unknown"),
        }
    }
}

/// A struct to represent the parsed cfg string.
#[derive(Eq, PartialEq, Hash, Ord, PartialOrd, Clone, Debug)]
pub struct Cfg(CfgExpr);

impl Cfg {
    /// Parses rust cfg attribute syntax.
    ///
    /// # Examples
    /// ``` rust
    /// use rust_cfg_parser::{parse, CfgValue};
    ///
    /// let expr = parse("cfg(windows)").unwrap();
    ///
    /// let matches = expr.matches(&[CfgValue::Name("linux".to_string())]);
    /// assert_eq!(false, matches);
    /// ```
    pub fn matches(&self, cfg: &[CfgValue]) -> bool {
        match &self.0 {
            CfgExpr::All(e) => e.iter().all(|e| e.matches(cfg)),
            CfgExpr::Any(e) => e.iter().any(|e| e.matches(cfg)),
            CfgExpr::Not(e) => !e.matches(cfg),
            CfgExpr::Value(e) => cfg.contains(e),
        }
    }
}

impl fmt::Display for Cfg {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "cfg({})", self.0)
    }
}

#[doc(hidden)]
#[inline]
fn is_indent_start(ch: char) -> bool {
    ch == '_' || ch.is_ascii_alphabetic()
}

#[doc(hidden)]
#[inline]
fn is_indent_rest(ch: char) -> bool {
    is_indent_start(ch) || ch.is_ascii_digit()
}

#[doc(hidden)]
fn parse_expr(tokens: &[CfgToken], idx: &mut usize) -> Result<CfgExpr, CfgParseError> {
    if *idx < tokens.len() {
        match tokens[*idx] {
            CfgToken::LeftParen | CfgToken::RightParen | CfgToken::Space | CfgToken::Comma => {
                if *idx == 0 && tokens[*idx] == CfgToken::RightParen {
                    return Err(CfgParseError::new(
                        CfgParseErrorKind::ExpectedLeftParentheses,
                    ));
                }
                *idx += 1;
                parse_expr(tokens, idx)
            }
            CfgToken::Ident(op @ "all") | CfgToken::Ident(op @ "any") => {
                *idx += 1;
                let mut entries: Vec<CfgExpr> = vec![];
                if tokens[*idx] == CfgToken::LeftParen {
                    while tokens[*idx] != CfgToken::RightParen {
                        entries.push(parse_expr(tokens, idx).unwrap());
                        *idx += 1;
                    }
                } else {
                    return Err(CfgParseError::new(
                        CfgParseErrorKind::ExpectedLeftParentheses,
                    ));
                }
                if op == "all" {
                    Ok(CfgExpr::All(entries))
                } else {
                    Ok(CfgExpr::Any(entries))
                }
            }
            CfgToken::Ident("not") => {
                *idx += 1;
                if tokens[*idx] != CfgToken::LeftParen {
                    return Err(CfgParseError::new(
                        CfgParseErrorKind::ExpectedLeftParentheses,
                    ));
                }
                Ok(CfgExpr::Not(Box::new(parse_expr(tokens, idx).unwrap())))
            }
            CfgToken::Ident(k) => {
                *idx += 1;
                if tokens[*idx] == CfgToken::Equals {
                    *idx += 1;
                    if let CfgToken::String(v) = tokens[*idx] {
                        Ok(CfgExpr::Value(CfgValue::KeyPair(
                            k.to_string(),
                            v.to_string(),
                        )))
                    } else {
                        Err(CfgParseError::new(CfgParseErrorKind::ExpectedString))
                    }
                } else {
                    Ok(CfgExpr::Value(CfgValue::Name(k.to_string())))
                }
            }
            CfgToken::String(_) => Err(CfgParseError::new(CfgParseErrorKind::UnExpectedString)),
            _ => Err(CfgParseError::new(CfgParseErrorKind::IncompatibleString)),
        }
    } else {
        Err(CfgParseError::new(CfgParseErrorKind::OutOfBounds))
    }
}

/// Parses a string rust cfg attribute syntax to an expression that can be evaluated.
///
/// # Examples
/// ``` rust
/// use rust_cfg_parser::{parse, CfgValue};
///
/// let expr = parse("cfg(windows)").unwrap();
///
/// let matches = expr.matches(&[CfgValue::Name("linux".to_string())]);
/// assert_eq!(false, matches);
///
/// let matches = expr.matches(&[CfgValue::Name("windows".to_string())]);
/// assert_eq!(true, matches);
/// ```
pub fn parse(input: &str) -> Result<Cfg, CfgParseError> {
    let expr = if input.starts_with("cfg") {
        let input = input.strip_prefix("cfg").unwrap().trim();
        let mut input_peekable = input.char_indices().peekable();
        let mut paren_count = 0;
        let mut parent_count_reset = false;
        let mut tokens: Vec<CfgToken> = Vec::new();
        loop {
            let tok = match input_peekable.next() {
                Some((_, '(')) => {
                    paren_count += 1;
                    if parent_count_reset {
                        CfgToken::Unknown
                    } else {
                        CfgToken::LeftParen
                    }
                }
                Some((_, ')')) => {
                    paren_count -= 1;
                    if paren_count == 0 {
                        parent_count_reset = true;
                    }
                    CfgToken::RightParen
                }
                Some((_, '=')) => CfgToken::Equals,
                Some((_, ',')) => CfgToken::Comma,
                Some((_, ' ')) => CfgToken::Space,
                Some((start, '\"')) => {
                    let mut stop = 0;
                    while input_peekable.peek().is_some() {
                        let (end, ch) = input_peekable.peek().unwrap();
                        if *ch == '\"' {
                            stop = *end;
                            input_peekable.next();
                            break;
                        } else {
                            input_peekable.next();
                        }
                    }
                    if stop == 0 {
                        CfgToken::Unknown
                    } else {
                        CfgToken::String(&input[start + 1..stop])
                    }
                }
                Some((start, ch)) if is_indent_start(ch) => {
                    let mut stop = 0;
                    while input_peekable.peek().is_some() {
                        let (end, ch) = input_peekable.peek().unwrap();
                        if !is_indent_rest(*ch) {
                            stop = *end;
                            break;
                        } else {
                            input_peekable.next();
                        }
                    }
                    if stop != 0 {
                        CfgToken::Ident(&input[start..stop])
                    } else {
                        CfgToken::Ident(&input[start..])
                    }
                }
                _ => CfgToken::Unknown,
            };
            if tok == CfgToken::Unknown {
                tokens.push(tok);
                break;
            }
            if tok != CfgToken::Space {
                tokens.push(tok);
            }
        }

        if parent_count_reset && paren_count > 0 {
            Err(CfgParseError::new(CfgParseErrorKind::IncompatibleString))
        } else if paren_count != 0 {
            Err(CfgParseError::new(CfgParseErrorKind::UnBalancedParentheses))
        } else {
            parse_expr(&tokens, &mut 0)
        }
    } else {
        Err(CfgParseError::new(CfgParseErrorKind::IncompatibleString))
    };
    match expr {
        Ok(expr) => Ok(Cfg(expr)),
        Err(e) => Err(e),
    }
}

#[cfg(test)]
mod tests {
    use crate::{parse, CfgParseErrorKind, CfgValue};

    #[test]
    fn target_os_only() {
        let expr = parse("cfg(target_os = \"hermit\")").unwrap();
        assert!(!expr.matches(&[CfgValue::KeyPair(
            "target_os".to_string(),
            "freebsd".to_string()
        )]));
        assert!(expr.matches(&[CfgValue::KeyPair(
            "target_os".to_string(),
            "hermit".to_string()
        )]));
    }

    #[test]
    fn os_only() {
        let expr = parse("cfg(windows)").unwrap();
        assert!(!expr.matches(&[CfgValue::Name("linux".to_string())]));
        assert!(expr.matches(&[CfgValue::Name("windows".to_string())]));
    }

    #[test]
    fn not_os_only() {
        let expr = parse("cfg(not( windows ))").unwrap();
        assert!(expr.matches(&[CfgValue::Name("linux".to_string())]));
        assert!(!expr.matches(&[CfgValue::Name("windows".to_string())]));
    }

    #[test]
    fn any_one_os() {
        let expr = parse("cfg(any (linux, windows))").unwrap();
        assert!(expr.matches(&[CfgValue::Name("linux".to_string())]));
        assert!(expr.matches(&[CfgValue::Name("windows".to_string())]));
        assert!(!expr.matches(&[CfgValue::Name("freebsd".to_string())]));
    }

    #[test]
    fn all_any() {
        let expr = parse("cfg(all(any(target_arch =\"x86_64\", target_arch = \"aarch64\"), target_os = \"hermit\"))").unwrap();
        assert!(expr.matches(&[
            CfgValue::KeyPair("target_arch".to_string(), "x86_64".to_string()),
            CfgValue::KeyPair("target_os".to_string(), "hermit".to_string())
        ]));
        assert!(!expr.matches(&[
            CfgValue::KeyPair("target_arch".to_string(), "i686".to_string()),
            CfgValue::KeyPair("target_os".to_string(), "freebsd".to_string())
        ]));
    }

    #[test]
    fn all_any_any() {
        let expr = parse("cfg(all(any(target_arch =\"x86_64\", target_arch   =   \"aarch64\"),any(target_feature=\"sse\",target_feature=\"sse2\"), target_os = \"hermit\"))").unwrap();
        assert!(expr.matches(&[
            CfgValue::KeyPair("target_arch".to_string(), "x86_64".to_string()),
            CfgValue::KeyPair("target_feature".to_string(), "sse2".to_string()),
            CfgValue::KeyPair("target_os".to_string(), "hermit".to_string())
        ]));
        assert!(!expr.matches(&[
            CfgValue::KeyPair("target_arch".to_string(), "x86_64".to_string()),
            CfgValue::KeyPair("target_feature".to_string(), "sse4.1".to_string()),
            CfgValue::KeyPair("target_os".to_string(), "hermit".to_string())
        ]));
        assert!(!expr.matches(&[
            CfgValue::KeyPair("target_arch".to_string(), "i686".to_string()),
            CfgValue::KeyPair("target_os".to_string(), "freebsd".to_string())
        ]));
    }

    #[test]
    fn all_features() {
        let expr = parse("cfg(all(all(target_feature =\"sse\", target_feature = \"sse2\", target_feature = \"sse4.1\"), target_os = \"windows\"))").unwrap();
        assert!(!expr.matches(&[
            CfgValue::KeyPair("target_feature".to_string(), "sse2".to_string()),
            CfgValue::KeyPair("target_feature".to_string(), "fsx4".to_string()),
            CfgValue::KeyPair("target_os".to_string(), "windows".to_string())
        ]));
        assert!(expr.matches(&[
            CfgValue::KeyPair("target_feature".to_string(), "sse".to_string()),
            CfgValue::KeyPair("target_feature".to_string(), "sse2".to_string()),
            CfgValue::KeyPair("target_feature".to_string(), "sse4.1".to_string()),
            CfgValue::KeyPair("target_os".to_string(), "windows".to_string())
        ]));
    }

    #[test]
    fn to_string() {
        let expr = parse("cfg( any (linux, windows))").unwrap();
        assert_eq!("cfg(any(linux, windows))", expr.to_string());
    }

    #[test]
    fn incompatible_string() {
        let kind = parse("cfg1(target_os = \"hermit\")").unwrap_err().kind;
        assert_eq!(CfgParseErrorKind::IncompatibleString, kind);

        let kind = parse("cfg(linux), windows(some)").unwrap_err().kind;
        assert_eq!(CfgParseErrorKind::IncompatibleString, kind);
    }

    #[test]
    fn unexpected_string() {
        let kind = parse("cfg(\"target_os\" = \"hermit\")").unwrap_err().kind;
        assert_eq!(CfgParseErrorKind::UnExpectedString, kind);
    }

    #[test]
    fn expected_string() {
        let kind = parse("cfg(target_os=hermit)").unwrap_err().kind;
        assert_eq!(CfgParseErrorKind::ExpectedString, kind);
    }

    #[test]
    fn unbalanced_parentheses() {
        let kind = parse("cfg(any (linux, windows)").unwrap_err().kind;
        assert_eq!(CfgParseErrorKind::UnBalancedParentheses, kind);
    }

    #[test]
    fn expected_left_parentheses() {
        let kind = parse("cfg)(any (linux, windows)").unwrap_err().kind;
        assert_eq!(CfgParseErrorKind::ExpectedLeftParentheses, kind);
    }
}
