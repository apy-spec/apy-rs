//! The APY CLI used to validate data against the APY format and to generate the JSON Schema for the format.
use apy::{Apy, ParseApyError};
use clap::{Parser, Subcommand};
#[cfg(feature = "schemars")]
use schemars;
use std::cmp::PartialEq;
use std::fs::File;
use std::path::{Path, PathBuf};
use std::process::exit;

/// The APY CLI.
#[derive(Debug, Parser)]
#[command(version, about, long_about)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

// The APY formats.
#[derive(Clone, PartialEq, Eq, Debug, clap::ValueEnum)]
enum FileFormat {
    Auto,
    Json,
    #[cfg(feature = "yaml")]
    Yaml,
}

impl FileFormat {
    /// Determines the file format based on the file extension of the given path.
    fn from_path(path: &Path) -> Option<Self> {
        if path.ends_with(".json") {
            return Some(FileFormat::Json);
        }

        #[cfg(feature = "yaml")]
        if path.ends_with(".yaml") || path.ends_with(".yml") {
            return Some(FileFormat::Yaml);
        }

        None
    }

    /// Reads an APY from the given reader according to the specified file format.
    fn read(self, reader: impl std::io::Read) -> Result<Apy, ParseApyError> {
        match self {
            FileFormat::Auto => {
                #[cfg(feature = "yaml")]
                return Apy::from_yaml_reader(reader);
                #[cfg(not(feature = "yaml"))]
                return Apy::from_json_reader(reader);
            }
            FileFormat::Json => Apy::from_json_reader(reader),
            #[cfg(feature = "yaml")]
            FileFormat::Yaml => Apy::from_yaml_reader(reader),
        }
    }
}

/// The APY CLI commands.
#[derive(Debug, Subcommand)]
enum Commands {
    #[cfg(feature = "schemars")]
    #[command(about = "Generate the JSON Schema for the APY format. Exit 1 or 2 on failure.")]
    JsonSchema {
        #[arg(help = "Path to the output file or leave empty to write to stdout")]
        output_path: Option<PathBuf>,
    },
    #[command(about = "Validate an APY file and display its version. Exit 1 or 2 on failure.")]
    Validate {
        #[arg(help = "The file format", short, long, value_enum, default_value_t = FileFormat::Auto
        )]
        format: FileFormat,
        #[arg(help = "Path to the input file or leave empty to read from stdin")]
        input_path: Option<PathBuf>,
    },
}

fn main() {
    let args = Cli::parse();

    match args.command {
        #[cfg(feature = "schemars")]
        Commands::JsonSchema { output_path } => {
            let schema = schemars::schema_for!(apy::Apy);

            let write_result = match output_path {
                Some(path) => match File::create(&path) {
                    Ok(file) => serde_json::to_writer_pretty(file, &schema)
                        .map(|_| "JSON Schema written to file successfully"),
                    Err(error) => {
                        eprintln!("Failed to create file: {}", error);
                        exit(2);
                    }
                },
                None => serde_json::to_writer_pretty(std::io::stdout(), &schema).map(|_| ""),
            };

            match write_result {
                Ok(message) => println!("{}", message),
                Err(error) => {
                    eprintln!("Failed to write JSON Schema: {}", error);
                    exit(1);
                }
            }
        }
        Commands::Validate {
            mut format,
            input_path,
        } => {
            let apy_result = match input_path {
                Some(path) => match File::open(&path) {
                    Ok(file) => {
                        if format == FileFormat::Auto {
                            format = FileFormat::from_path(&path).unwrap_or(FileFormat::Auto);
                        }
                        format.read(file)
                    }
                    Err(error) => {
                        eprintln!("Failed to open file: {}", error);
                        exit(2);
                    }
                },
                None => format.read(std::io::stdin()),
            };

            let Ok(apy) = apy_result else {
                eprintln!("Invalid APY data");
                exit(1);
            };

            println!("{}", apy.version());
        }
    }
}
