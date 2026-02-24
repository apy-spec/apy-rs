# APY

A Rust library for working with the APY specification format, providing data structures and
serialization/deserialization capabilities for different versions of APY.

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
apy = { git = "https://github.com/apy-spec/apy-rs.git" }
```

### Features

- `schemars` - Generate JSON Schema for APY data structures.
- `yaml` - Support for YAML serialization/deserialization of APY format.
- `cli` - Command-line interface for working with APY format.

## Usage

### API

```rust
use serde_json;
use apy::Apy;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let path = "path/to/apy.json";

    let apy = Apy::from_json_reader(File::open(&path)?)?;

    println!("{:#?}", apy);
}
```

### CLI

You can use the `apy` CLI to validate APY files and generate JSON Schema (`schemars` feature required):

```sh
# Validate an APY file
apy validate path/to/apy.json

# Generate the JSON Schema for the APY format (`schemars` feature required)
apy json-schema apy.schema.json
```

## License

Licensed under either of

* Apache License, Version 2.0
  ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
* MIT license
  ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
