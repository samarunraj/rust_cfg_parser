# rust_cfg_parser - Parser for rust cfg() expression

[![Build Status](https://github.com/samarunraj/rust_cfg_parser/actions/workflows/ci.yml/badge.svg)](https://github.com/samarunraj/rust_cfg_parser/actions?workflow=CI)
[![Crates.io](https://img.shields.io/crates/v/rust_cfg_parser.svg)](https://crates.io/crates/rust_cfg_parser)
[![Docs](https://docs.rs/rust_cfg_parser/badge.svg)](https://docs.rs/rust_cfg_parser)

## Usage

To use `rust_cfg_parser` in your project, add the following to your Cargo.toml:

``` toml
[dependencies]
rust_cfg_parser = "0.1.0"
```

## Example

```rust
use rust_cfg_parser::{CfgValue, parse};

let expr = parse("cfg(windows)").unwrap();

let matches = expr.matches(&[CfgValue::Name("linux".to_string())]);
assert_eq!(false, matches);

let matches = expr.matches(&[CfgValue::Name("windows".to_string())]);
assert_eq!(true, matches);

let expr = parse("cfg(all(any(target_arch =\"x86_64\", target_arch = \"aarch64\"), target_os = \"windows\"))").unwrap();
assert_eq!(
    true,
    expr.matches(&[
        CfgValue::KeyPair("target_arch".to_string(), "x86_64".to_string()),
        CfgValue::KeyPair("target_os".to_string(), "windows".to_string())
    ])
);
```

License: MIT