//! The structures used to represent the APY format version `1.0.0`.
//!
//! # Examples
//!
//! ```rust
//! # use std::error::Error;
//! # fn main() -> Result<(), Box<dyn Error>> {
//! use std::collections::BTreeMap;
//! use apy::OneOrMany;
//! use apy::v1::{Identifier, QualifiedName, Type, Parameter, ParameterKind, Parameters, Generic, GenericKind, Exception, Signature, Function, Attribute, Variable, Module, ApyV1, ModuleAttributes};
//!
//! let identifier = Identifier::try_from("my_variable")?;
//! let int_type = Type::new(QualifiedName::try_from("int")?);
//! let variable = Attribute::Variable(Variable::new(int_type));
//!
//! let module = Module::new(
//!     ModuleAttributes::try_from(BTreeMap::from_iter([(identifier, OneOrMany::one(variable))]))?,
//!     ModuleAttributes::new(),
//! );
//!
//! let module_name = QualifiedName::try_from("my_module.submodule")?;
//! let mut apy = ApyV1::new();
//! apy.modules.insert(module_name, module);
//! #     Ok(())
//! # }
//! ```
use crate::{FromEmptyIteratorError, OneOrMany, Value, default_true};
#[cfg(feature = "schemars")]
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashSet};
use std::fmt::Display;
use std::ops::Deref;
use thiserror::Error;
use unicode_ident::{is_xid_continue, is_xid_start};
use unicode_normalization::UnicodeNormalization;

/// The error returned when trying to convert an invalid Python identifier to an `Identifier`.
#[derive(Debug, Error)]
#[error("Tried to convert an invalid Python identifier")]
pub struct FromInvalidIdentifierError;

/// A Python identifier, which is a name used to identify a variable, function, class, module,
/// or other object in Python.
///
/// # References:
/// - [PEP 3131 – Supporting Non-ASCII Identifiers](https://peps.python.org/pep-3131/)
/// - [Lexical analysis - Names (identifiers and keywords)](https://docs.python.org/3/reference/lexical_analysis.html#names-identifiers-and-keywords)
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Identifier {
    // Invariant: name should be a valid Python identifier
    name: String,
}

impl TryFrom<&str> for Identifier {
    type Error = FromInvalidIdentifierError;

    /// Tries to convert a string into an `Identifier`, returning an error if the string is not
    /// a valid Python identifier.
    ///
    /// # Errors
    ///
    /// Returns `FromInvalidIdentifierError` if the string is empty, is a Python keyword,
    /// or does not match the syntax of a valid Python identifier.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use apy::v1::Identifier;
    ///
    /// assert!(Identifier::try_from("valid_identifier").is_ok());
    ///
    /// assert!(Identifier::try_from("").is_err());
    /// assert!(Identifier::try_from("for").is_err());
    /// assert!(Identifier::try_from("1invalid").is_err());
    /// ```
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let normalized_value = value.nfkc().collect::<String>();

        if normalized_value.is_empty()
            || matches!(
                normalized_value.as_str(),
                "False"
                    | "await"
                    | "else"
                    | "import"
                    | "pass"
                    | "None"
                    | "break"
                    | "except"
                    | "in"
                    | "raise"
                    | "True"
                    | "class"
                    | "finally"
                    | "is"
                    | "return"
                    | "and"
                    | "continue"
                    | "for"
                    | "lambda"
                    | "try"
                    | "as"
                    | "def"
                    | "from"
                    | "nonlocal"
                    | "while"
                    | "assert"
                    | "del"
                    | "global"
                    | "not"
                    | "with"
                    | "async"
                    | "elif"
                    | "if"
                    | "or"
                    | "yield"
            )
        {
            return Err(FromInvalidIdentifierError);
        }

        let mut chars = normalized_value.chars();

        let is_valid_identifier = if let Some(first) = chars.next() {
            (first == '_' || is_xid_start(first)) && chars.all(|c| c == '_' || is_xid_continue(c))
        } else {
            false
        };

        if !is_valid_identifier {
            return Err(FromInvalidIdentifierError);
        }

        Ok(Identifier {
            name: normalized_value,
        })
    }
}

impl From<Identifier> for String {
    /// Unwraps the `String` from the `Identifier`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::v1::Identifier;
    ///
    /// let identifier = Identifier::try_from("valid_identifier")?;
    ///
    /// let identifier_string = String::from(identifier);
    ///
    /// assert_eq!(identifier_string, "valid_identifier");
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    fn from(value: Identifier) -> Self {
        value.name
    }
}

impl AsRef<str> for Identifier {
    fn as_ref(&self) -> &str {
        &self.name
    }
}

impl Deref for Identifier {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.name
    }
}

impl Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name.fmt(f)
    }
}

/// The error returned when trying to convert an invalid qualified name to a `QualifiedName`.
#[derive(Debug, Error)]
pub enum FromInvalidQualifiedNameError {
    #[error("The qualified name contains an invalid identifier.")]
    ContainInvalidIdentifier(#[from] FromInvalidIdentifierError),
    #[error("The qualified name is empty.")]
    IsEmptyQualifiedName(#[from] FromEmptyIteratorError),
}

/// A qualified name, which is a dot-separated sequence of identifiers used to identify a module,
/// class, function, or other object in Python.
///
/// # References:
/// - [PEP 3155 – Qualified name for classes and functions](https://peps.python.org/pep-3155/)
/// - [Glossary - Qualified name](https://docs.python.org/3/glossary.html#term-qualified-name)
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
#[serde(try_from = "&str", into = "String")]
pub struct QualifiedName {
    pub identifiers: OneOrMany<Identifier>,
}

impl QualifiedName {
    /// Creates a new `QualifiedName` with the given identifiers.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::v1::{Identifier, QualifiedName};
    /// use apy::OneOrMany;
    ///
    /// let qualified_name = QualifiedName::new(OneOrMany::one(Identifier::try_from("my_module")?));
    ///
    /// assert_eq!(qualified_name.join(), "my_module");
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn new(identifiers: OneOrMany<Identifier>) -> Self {
        Self { identifiers }
    }

    /// Joins the identifiers of the qualified name with dots to create a string representation
    /// of the qualified name.
    pub fn join(&self) -> String {
        self.identifiers
            .iter()
            .map(|identifier| identifier.as_ref())
            .collect::<Vec<_>>()
            .join(".")
    }
}

impl TryFrom<&str> for QualifiedName {
    type Error = FromInvalidQualifiedNameError;

    /// Tries to convert a `&str` into a `QualifiedName`, returning an error if any of the identifiers
    /// in the qualified name are invalid or if the qualified name is empty.
    ///
    /// # Errors
    ///
    /// Returns `FromInvalidQualifiedNameError::ContainInvalidIdentifier` if any of the identifiers
    /// in the qualified name are invalid, or `FromInvalidQualifiedNameError::IsEmptyQualifiedName`
    /// if the qualified name is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use apy::v1::QualifiedName;
    ///
    /// assert!(QualifiedName::try_from("valid_qualified_name").is_ok());
    /// assert!(QualifiedName::try_from("valid.qualified.name").is_ok());
    ///
    /// assert!(QualifiedName::try_from("invalid..qualified.name").is_err());
    /// assert!(QualifiedName::try_from("invalid.qualified.name.").is_err());
    /// assert!(QualifiedName::try_from(".invalid.qualified.name").is_err());
    /// assert!(QualifiedName::try_from("").is_err());
    /// ```
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Ok(Self::new(OneOrMany::try_from(
            value
                .split('.')
                .map(Identifier::try_from)
                .collect::<Result<Vec<_>, _>>()?,
        )?))
    }
}

impl From<QualifiedName> for String {
    /// Joins the `QualifiedName` into a `String`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::v1::QualifiedName;
    ///
    /// let qualified_name = QualifiedName::try_from("valid.qualified.name")?;
    ///
    /// let qualified_name_string = String::from(qualified_name);
    ///
    /// assert_eq!(qualified_name_string, "valid.qualified.name");
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    fn from(value: QualifiedName) -> String {
        value.join()
    }
}

impl Display for QualifiedName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.join().fmt(f)
    }
}

/// Other Python values which are constants or that cannot be represented.
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
pub enum OtherPythonValue {
    #[serde(rename = "None")]
    None,
    #[serde(rename = "...")]
    Ellipsis,
    #[serde(rename = "?")]
    Unknown,
}

/// A Python value, which can be a primitive value (e.g. an integer, float, complex number, or string),
/// a collection (e.g. a list or a dictionary), a constant value (e.g. `None` or `...`) or
/// an unknown value that cannot be represented.
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
#[serde(untagged)]
pub enum PythonValue {
    Int { int: String },
    Float { float: String },
    Complex { complex: String },
    Str { str: String },
    Tuple { tuple: Vec<PythonValue> },
    List { list: Vec<PythonValue> },
    Dict { dict: BTreeMap<String, PythonValue> },
    Other(OtherPythonValue),
}

/// A type argument, which can be a type or a value (e.g. a literal).
///
/// # References:
/// - [PEP 484 - Type Hints](https://peps.python.org/pep-0484/)
/// - [PEP 593 – Flexible function and variable annotations](https://peps.python.org/pep-0593/)
/// - [Typing module - Annotated](https://typing.python.org/en/latest/spec/qualifiers.html#annotated)
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[serde(untagged)]
pub enum TypeArgument {
    Type(Type),
    Value { value: PythonValue },
}

/// A type which is a reference to a qualified name with optional type arguments.
///
/// # References:
/// - [PEP 484 - Type Hints](https://peps.python.org/pep-0484/)
/// - [PEP 585 - Type Hinting Generics In Standard Collections](https://peps.python.org/pep-0585/)
/// - [Glossary - Type hint](https://docs.python.org/3/glossary.html#term-type-hint)
/// - [Glossary - Type](https://docs.python.org/3/glossary.html#term-type)
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct Type {
    pub id: QualifiedName,

    /// Reference to the index of the attribute in the history.
    /// Used when type are overridden in the same namespace.
    #[serde(default)]
    pub history_index: usize,

    #[serde(default)]
    pub arguments: Vec<TypeArgument>,

    #[serde(default, flatten)]
    pub extensions: BTreeMap<String, Value>,
}

impl Type {
    /// Creates a new `Type` with the given qualified name and default values for the other fields.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::v1::{QualifiedName, Type};
    ///
    /// let my_type = Type::new(QualifiedName::try_from("int")?);
    ///
    /// assert_eq!(my_type.id.join(), "int");
    /// assert_eq!(my_type.history_index, 0);
    /// assert!(my_type.arguments.is_empty());
    /// assert!(my_type.extensions.is_empty());
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn new(id: QualifiedName) -> Self {
        Self {
            id,
            history_index: 0,
            arguments: Vec::new(),
            extensions: BTreeMap::new(),
        }
    }
}

/// The visibility of a module, class, function, or other item in Python.
///
/// It can be public or non-public (internal or subclass).
///
/// # References:
/// - [PEP 8 - Style Guide for Python Code](https://peps.python.org/pep-0008/#public-and-internal-interfaces)
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
pub enum Visibility {
    /// Accessible from anywhere.
    #[serde(rename = "PUBLIC")]
    Public,

    /// Accessible within the class, its subclasses and the same module/package.
    ///
    /// Only applicable to class attributes.
    #[serde(rename = "SUBCLASS")]
    Subclass,

    /// Accessible only within the same module/package.
    #[serde(rename = "INTERNAL")]
    Internal,
}

impl Default for Visibility {
    /// Returns the default visibility, which is `Public`.
    fn default() -> Self {
        Visibility::Public
    }
}

/// The kind of function parameter.
///
/// # References:
/// - [PEP 484 - Type Hints](https://peps.python.org/pep-0484/)
/// - [PEP 570 - Python Positional-Only Parameters](https://peps.python.org/pep-0570/)
/// - [PEP 3102 - Keyword-Only Arguments](https://peps.python.org/pep-3102/)
/// - [Glossary - Parameter](https://docs.python.org/3/glossary.html#term-parameter)
/// - [Inspect module - Parameter kind](https://docs.python.org/3/library/inspect.html#inspect.Parameter.kind)
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
pub enum ParameterKind {
    #[serde(rename = "POSITIONAL_ONLY")]
    PositionalOnly,

    #[serde(rename = "POSITIONAL_OR_KEYWORD")]
    PositionalOrKeyword,

    #[serde(rename = "VAR_POSITIONAL")]
    VarPositional,

    #[serde(rename = "KEYWORD_ONLY")]
    KeywordOnly,

    #[serde(rename = "VAR_KEYWORD")]
    VarKeyword,
}

/// A function parameter.
///
/// # References:
/// - [PEP 484 - Type Hints](https://peps.python.org/pep-0484/)
/// - [PEP 362 – Function Signature Object](https://peps.python.org/pep-0362/)
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct Parameter {
    pub name: Identifier,

    pub kind: ParameterKind,

    #[serde(rename = "type")]
    pub parameter_type: Type,

    #[serde(default)]
    pub description: String,

    #[serde(rename = "optional", default)]
    pub is_optional: bool,

    #[serde(rename = "deprecated", default)]
    pub is_deprecated: bool,

    #[serde(default, flatten)]
    pub extensions: BTreeMap<String, Value>,
}

impl Parameter {
    /// Creates a new `Parameter` with the given name, kind, and type, and default values for the other fields.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::v1::{Identifier, QualifiedName, Type, ParameterKind, Parameter};
    ///
    /// let parameter = Parameter::new(
    ///     Identifier::try_from("x")?,
    ///     ParameterKind::PositionalOnly,
    ///     Type::new(QualifiedName::try_from("int")?),
    /// );
    ///
    /// assert_eq!(parameter.name.as_ref(), "x");
    /// assert_eq!(parameter.kind, ParameterKind::PositionalOnly);
    /// assert_eq!(parameter.parameter_type.id.join(), "int");
    /// assert!(parameter.description.is_empty());
    /// assert!(!parameter.is_optional);
    /// assert!(!parameter.is_deprecated);
    /// assert!(parameter.extensions.is_empty());
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn new(name: Identifier, kind: ParameterKind, parameter_type: Type) -> Self {
        Self {
            name,
            kind,
            parameter_type,
            description: String::new(),
            is_optional: false,
            is_deprecated: false,
            extensions: BTreeMap::new(),
        }
    }
}

/// The error returned when trying to convert a list of parameters into a `Parameters` struct.
#[derive(Debug, Error)]
pub enum FromParametersError {
    #[error(
        "The parameters are in an invalid order in regards to their kinds.
        The order should be: positional-only, positional-or-keyword, var-positional, keyword-only, var-keyword."
    )]
    IsInvalidOrder { parameters: Vec<Parameter> },
    #[error("Multiple parameters exist with the name {parameter_name}")]
    ContainMultipleParametersWithSameName {
        parameter_name: Identifier,
        parameters: Vec<Parameter>,
    },
    #[error("Multiple var-positional parameters exist, but only one is allowed.")]
    ContainMultipleVarPositionalParameters { parameters: Vec<Parameter> },
    #[error("Multiple var-keyword parameters exist, but only one is allowed.")]
    ContainMultipleVarKeywordParameters { parameters: Vec<Parameter> },
    #[error(
        "The parameter {parameter_name} is a var-positional parameter that should always be optional."
    )]
    HasNonOptionalVarPositional {
        parameter_name: Identifier,
        parameters: Vec<Parameter>,
    },
    #[error(
        "The parameter {parameter_name} is a var-keyword parameter that should always be optional."
    )]
    HasNonOptionalVarKeyword {
        parameter_name: Identifier,
        parameters: Vec<Parameter>,
    },
}

/// A list of function parameters that follows the rules for valid function parameters in Python.
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default, Serialize)]
#[serde(transparent)]
pub struct Parameters {
    list: Vec<Parameter>,
}

impl Parameters {
    /// Creates a new `Parameters` struct with an empty list of parameters.
    pub fn new() -> Self {
        Self::default()
    }
}

impl<'de> Deserialize<'de> for Parameters {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Ok(Parameters::try_from(Vec::deserialize(deserializer)?)
            .map_err(serde::de::Error::custom)?)
    }
}

impl TryFrom<Vec<Parameter>> for Parameters {
    type Error = FromParametersError;

    /// Tries to convert a list of parameters into a `Parameters` struct, returning an error if
    /// the parameters do not follow the rules for valid function parameters in Python.
    ///
    /// # Errors
    ///
    /// Returns `FromParametersError` if the list does not follow the rules for
    /// valid function parameters in Python.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::v1::{Identifier, QualifiedName, Parameter, ParameterKind, Parameters, Type};
    ///
    /// let parameters = vec![
    ///     Parameter::new(
    ///         Identifier::try_from("x")?,
    ///         ParameterKind::PositionalOnly,
    ///         Type::new(QualifiedName::try_from("int")?),
    ///     ),
    ///     Parameter::new(
    ///        Identifier::try_from("y")?,
    ///        ParameterKind::KeywordOnly,
    ///        Type::new(QualifiedName::try_from("str")?),
    ///     ),
    /// ];
    ///
    /// assert!(Parameters::try_from(parameters).is_ok());
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    fn try_from(value: Vec<Parameter>) -> Result<Self, Self::Error> {
        if !value.iter().map(|parameter| parameter.kind).is_sorted() {
            return Err(FromParametersError::IsInvalidOrder { parameters: value });
        }

        let mut seen_names: HashSet<&str> = HashSet::new();
        let mut has_var_positional_parameters = false;
        let mut has_var_keyword_parameters = false;

        for parameter in &value {
            if !seen_names.insert(&parameter.name) {
                return Err(FromParametersError::ContainMultipleParametersWithSameName {
                    parameter_name: parameter.name.clone(),
                    parameters: value,
                });
            }
            match parameter.kind {
                ParameterKind::VarPositional => {
                    if !parameter.is_optional {
                        return Err(FromParametersError::HasNonOptionalVarPositional {
                            parameter_name: parameter.name.clone(),
                            parameters: value,
                        });
                    }

                    if has_var_positional_parameters {
                        return Err(
                            FromParametersError::ContainMultipleVarPositionalParameters {
                                parameters: value,
                            },
                        );
                    } else {
                        has_var_positional_parameters = true;
                    }
                }
                ParameterKind::VarKeyword => {
                    if !parameter.is_optional {
                        return Err(FromParametersError::HasNonOptionalVarKeyword {
                            parameter_name: parameter.name.clone(),
                            parameters: value,
                        });
                    }

                    if has_var_keyword_parameters {
                        return Err(FromParametersError::ContainMultipleVarKeywordParameters {
                            parameters: value,
                        });
                    } else {
                        has_var_keyword_parameters = true;
                    }
                }
                _ => {}
            }
        }

        Ok(Self { list: value })
    }
}

impl From<Parameters> for Vec<Parameter> {
    /// Unwraps the `Vec<Parameter>` from the `Parameters`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::v1::{Identifier, QualifiedName, Type, Parameter, ParameterKind, Parameters};
    ///
    /// let parameters = Parameters::try_from(vec![
    ///     Parameter::new(
    ///         Identifier::try_from("x")?,
    ///         ParameterKind::PositionalOnly,
    ///         Type::new(QualifiedName::try_from("int")?),
    ///     ),
    ///     Parameter::new(
    ///        Identifier::try_from("y")?,
    ///        ParameterKind::KeywordOnly,
    ///        Type::new(QualifiedName::try_from("str")?),
    ///     ),
    /// ])?;
    ///
    /// let parameters_vec: Vec<Parameter> = Vec::from(parameters);
    ///
    /// assert_eq!(parameters_vec.len(), 2);
    /// assert_eq!(parameters_vec[0].name.as_ref(), "x");
    /// assert_eq!(parameters_vec[0].kind, ParameterKind::PositionalOnly);
    /// assert_eq!(parameters_vec[0].parameter_type.id.join(), "int");
    /// assert_eq!(parameters_vec[1].name.as_ref(), "y");
    /// assert_eq!(parameters_vec[1].kind, ParameterKind::KeywordOnly);
    /// assert_eq!(parameters_vec[1].parameter_type.id.join(), "str");
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    fn from(value: Parameters) -> Self {
        value.list
    }
}

impl AsRef<[Parameter]> for Parameters {
    fn as_ref(&self) -> &[Parameter] {
        &self.list
    }
}

impl Deref for Parameters {
    type Target = [Parameter];

    fn deref(&self) -> &Self::Target {
        &self.list
    }
}

/// The kind of generic type variable.
///
/// # References:
/// - [PEP 484 - Type Hints](https://peps.python.org/pep-0484/)
/// - [PEP 612 – Parameter Specification Variables](https://peps.python.org/pep-0612/)
/// - [PEP 646 – Variadic Generics](https://peps.python.org/pep-0646/)
/// - [Typing module - TypeVar](https://typing.python.org/en/latest/spec/generics.html#introduction)
/// - [Typing module - ParamSpec](https://typing.python.org/en/latest/spec/generics.html#paramspec)
/// - [Typing module - TypeVarTuple](https://typing.python.org/en/latest/spec/generics.html#typevartuple)
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
pub enum GenericKind {
    #[serde(rename = "TYPE_VAR")]
    TypeVar,

    #[serde(rename = "PARAM_SPEC")]
    ParamSpec,

    #[serde(rename = "TYPE_VAR_TUPLE")]
    TypeVarTuple,
}

/// A generic type variable, which can be used to define generic types and functions.
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct Generic {
    pub kind: GenericKind,

    #[serde(default)]
    pub bound: Option<Type>,

    #[serde(default)]
    pub constraints: Vec<Type>,

    #[serde(default)]
    pub default: Option<Type>,

    #[serde(rename = "covariant", default)]
    pub is_covariant: bool,

    #[serde(rename = "contravariant", default)]
    pub is_contravariant: bool,

    #[serde(rename = "deprecated", default)]
    pub is_deprecated: bool,

    #[serde(default)]
    pub visibility: Visibility,

    #[serde(default, flatten)]
    pub extensions: BTreeMap<String, Value>,
}

impl Generic {
    /// Creates a new `Generic` with the given kind and default values for the other fields.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use apy::v1::{Visibility, GenericKind, Generic};
    ///
    /// let generic = Generic::new(GenericKind::TypeVar);
    ///
    /// assert_eq!(generic.kind, GenericKind::TypeVar);
    /// assert!(generic.bound.is_none());
    /// assert!(generic.constraints.is_empty());
    /// assert!(generic.default.is_none());
    /// assert!(!generic.is_covariant);
    /// assert!(!generic.is_contravariant);
    /// assert!(!generic.is_deprecated);
    /// assert_eq!(generic.visibility, Visibility::Public);
    /// assert!(generic.extensions.is_empty());
    /// ```
    pub fn new(kind: GenericKind) -> Self {
        Self {
            kind,
            bound: None,
            constraints: Vec::new(),
            default: None,
            is_covariant: false,
            is_contravariant: false,
            is_deprecated: false,
            visibility: Visibility::Public,
            extensions: BTreeMap::new(),
        }
    }
}

/// An exception that can be raised.
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct Exception {
    pub exception_type: Type,

    #[serde(default)]
    pub description: String,

    #[serde(default, flatten)]
    pub extensions: BTreeMap<String, Value>,
}

impl Exception {
    /// Creates a new `Exception` with the given type and default values for the other fields.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::v1::{QualifiedName, Type, Exception};
    ///
    /// let exception = Exception::new(Type::new(QualifiedName::try_from("ValueError")?));
    ///
    /// assert_eq!(exception.exception_type.id.join(), "ValueError");
    /// assert!(exception.description.is_empty());
    /// assert!(exception.extensions.is_empty());
    /// #     Ok(())
    /// # }
    /// ```
    pub fn new(exception_type: Type) -> Self {
        Self {
            exception_type,
            description: String::new(),
            extensions: BTreeMap::new(),
        }
    }
}

/// A function or method signature.
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct Signature {
    pub return_type: Type,

    #[serde(default)]
    pub summary: String,

    #[serde(default)]
    pub description: String,

    #[serde(default)]
    pub generics: BTreeMap<String, Generic>,

    #[serde(default)]
    pub parameters: Parameters,

    #[serde(default)]
    pub raises: Vec<Exception>,

    #[serde(rename = "partial", default)]
    pub is_partial: bool,

    #[serde(rename = "pure", default)]
    pub is_pure: bool,

    #[serde(rename = "deprecated", default)]
    pub is_deprecated: bool,

    #[serde(default)]
    pub visibility: Visibility,

    #[serde(default, flatten)]
    pub extensions: BTreeMap<String, Value>,
}

impl Signature {
    /// Creates a new `Signature` with the given return type and default values for the other fields.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::v1::{QualifiedName, Type, Visibility, Signature};
    ///
    /// let signature = Signature::new(Type::new(QualifiedName::try_from("int")?));
    ///
    /// assert_eq!(signature.return_type.id.join(), "int");
    /// assert!(signature.summary.is_empty());
    /// assert!(signature.description.is_empty());
    /// assert!(signature.generics.is_empty());
    /// assert!(signature.parameters.is_empty());
    /// assert!(signature.raises.is_empty());
    /// assert!(!signature.is_partial);
    /// assert!(!signature.is_pure);
    /// assert!(!signature.is_deprecated);
    /// assert_eq!(signature.visibility, Visibility::Public);
    /// assert!(signature.extensions.is_empty());
    /// #     Ok(())
    /// # }
    /// ```
    pub fn new(return_type: Type) -> Self {
        Self {
            return_type,
            summary: String::new(),
            description: String::new(),
            generics: BTreeMap::new(),
            parameters: Parameters::default(),
            raises: Vec::new(),
            is_partial: false,
            is_pure: false,
            is_deprecated: false,
            visibility: Visibility::Public,
            extensions: BTreeMap::new(),
        }
    }
}

/// A function or method, which can have multiple signatures due to function overloading.
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct Function {
    pub signature: OneOrMany<Signature>,

    #[serde(rename = "async", default)]
    pub is_async: bool,

    #[serde(rename = "override", default)]
    pub is_overriding: bool,

    #[serde(rename = "abstract", default)]
    pub is_abstract: bool,

    #[serde(rename = "final", default)]
    pub is_final: bool,

    #[serde(default, flatten)]
    pub extensions: BTreeMap<String, Value>,
}

impl Function {
    /// Creates a new `Function` with the given signature and default values for the other fields.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::OneOrMany;
    /// use apy::v1::{QualifiedName, Type, Signature, Function};
    ///
    /// let function = Function::new(OneOrMany::one(Signature::new(Type::new(QualifiedName::try_from("int")?))));
    ///
    /// assert_eq!(function.signature.len(), 1);
    /// assert_eq!(function.signature[0].return_type.id.join(), "int");
    /// assert!(!function.is_async);
    /// assert!(!function.is_overriding);
    /// assert!(!function.is_abstract);
    /// assert!(!function.is_final);
    /// assert!(function.extensions.is_empty());
    /// #     Ok(())
    /// # }
    /// ```
    pub fn new(signature: OneOrMany<Signature>) -> Self {
        Self {
            signature,
            is_async: false,
            is_overriding: false,
            is_abstract: false,
            is_final: false,
            extensions: BTreeMap::new(),
        }
    }
}

/// A variable, which can be a module-level variable, a class attribute, or an instance attribute.
///
/// # References:
/// - [PEP 526 – Syntax for Variable Annotations](https://peps.python.org/pep-0526/)
/// - [Typing module - Annotated assignment statements](https://docs.python.org/3/reference/simple_stmts.html#annotated-assignment-statements)
/// - [Typing module - ClassVar](https://typing.python.org/en/latest/spec/class-compat.html#classvar)
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct Variable {
    #[serde(rename = "type")]
    pub variable_type: Type,

    #[serde(default)]
    pub description: String,

    #[serde(rename = "initialised", default = "default_true")]
    pub is_initialised: bool,

    #[serde(rename = "readonly", default)]
    pub is_readonly: bool,

    #[serde(rename = "final", default)]
    pub is_final: bool,

    #[serde(rename = "deprecated", default)]
    pub is_deprecated: bool,

    #[serde(default)]
    pub visibility: Visibility,

    #[serde(default, flatten)]
    pub extensions: BTreeMap<String, Value>,
}

impl Variable {
    /// Creates a new `Variable` with the given type and default values for the other fields.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::v1::{QualifiedName, Type, Visibility, Variable};
    ///
    /// let variable = Variable::new(Type::new(QualifiedName::try_from("int")?));
    ///
    /// assert_eq!(variable.variable_type.id.join(), "int");
    /// assert!(variable.description.is_empty());
    /// assert!(variable.is_initialised);
    /// assert!(!variable.is_readonly);
    /// assert!(!variable.is_final);
    /// assert!(!variable.is_deprecated);
    /// assert_eq!(variable.visibility, Visibility::Public);
    /// assert!(variable.extensions.is_empty());
    /// #     Ok(())
    /// # }
    /// ```
    pub fn new(variable_type: Type) -> Self {
        Self {
            variable_type,
            description: String::new(),
            is_initialised: true,
            is_readonly: false,
            is_final: false,
            is_deprecated: false,
            visibility: Visibility::Public,
            extensions: BTreeMap::new(),
        }
    }
}

/// A type alias, which is a name that refers to a type.
///
/// # References:
/// - [PEP 484 - Type Hints](https://peps.python.org/pep-0484/#type-aliases)
/// - [PEP 613 – Explicit Type Aliases](https://peps.python.org/pep-0613/)
/// - [PEP 695 – Type Parameter Syntax](https://peps.python.org/pep-0695/)
/// - [Typing module - Type aliases](https://typing.python.org/en/latest/spec/aliases.html#type-aliases)
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct TypeAlias {
    pub alias: Type,

    #[serde(default)]
    pub description: String,

    #[serde(default)]
    pub generics: BTreeMap<String, Generic>,

    #[serde(rename = "deprecated", default)]
    pub is_deprecated: bool,

    #[serde(default)]
    pub visibility: Visibility,

    #[serde(default, flatten)]
    pub extensions: BTreeMap<String, Value>,
}

impl TypeAlias {
    /// Creates a new `TypeAlias` with the given alias and default values for the other fields.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::v1::{QualifiedName, Type, Visibility, TypeAlias};
    ///
    /// let type_alias = TypeAlias::new(Type::new(QualifiedName::try_from("int")?));
    ///
    /// assert_eq!(type_alias.alias.id.join(), "int");
    /// assert!(type_alias.description.is_empty());
    /// assert!(type_alias.generics.is_empty());
    /// assert!(!type_alias.is_deprecated);
    /// assert_eq!(type_alias.visibility, Visibility::Public);
    /// assert!(type_alias.extensions.is_empty());
    /// #     Ok(())
    /// # }
    /// ```
    pub fn new(alias: Type) -> Self {
        Self {
            alias,
            description: String::new(),
            generics: BTreeMap::new(),
            is_deprecated: false,
            visibility: Visibility::Public,
            extensions: BTreeMap::new(),
        }
    }
}

/// A class, which can have multiple base classes, attributes, and methods.
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default, Serialize, Deserialize)]
pub struct Class {
    #[serde(default)]
    pub summary: String,

    #[serde(default)]
    pub description: String,

    #[serde(default)]
    pub generics: BTreeMap<String, Generic>,

    #[serde(default)]
    pub bases: Vec<Type>,

    #[serde(default)]
    pub keyword_arguments: BTreeMap<String, PythonValue>,

    #[serde(default)]
    pub raises: Vec<Exception>,

    #[serde(rename = "partial", default)]
    pub is_partial: bool,

    #[serde(rename = "abstract", default)]
    pub is_abstract: bool,

    #[serde(rename = "final", default)]
    pub is_final: bool,

    #[serde(rename = "deprecated", default)]
    pub is_deprecated: bool,

    #[serde(default)]
    pub visibility: Visibility,

    #[serde(default)]
    pub attributes: BTreeMap<Identifier, OneOrMany<Attribute>>,

    #[serde(default)]
    pub typing_attributes: BTreeMap<Identifier, OneOrMany<Attribute>>,

    #[serde(default, flatten)]
    pub extensions: BTreeMap<String, Value>,
}

impl Class {
    /// Creates a new `Class` with default values for all fields.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use apy::v1::{Visibility, Class};
    ///
    /// let class = Class::new();
    ///
    /// assert!(class.summary.is_empty());
    /// assert!(class.description.is_empty());
    /// assert!(class.generics.is_empty());
    /// assert!(class.bases.is_empty());
    /// assert!(class.keyword_arguments.is_empty());
    /// assert!(class.raises.is_empty());
    /// assert!(!class.is_partial);
    /// assert!(!class.is_abstract);
    /// assert!(!class.is_final);
    /// assert!(!class.is_deprecated);
    /// assert_eq!(class.visibility, Visibility::Public);
    /// assert!(class.attributes.is_empty());
    /// assert!(class.typing_attributes.is_empty());
    /// assert!(class.extensions.is_empty());
    /// ```
    pub fn new() -> Self {
        Self::default()
    }
}

/// An imported module, which is a reference to a module that is imported in the current namespace.
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct ImportedModule {
    pub module: QualifiedName,

    #[serde(rename = "deprecated", default)]
    pub is_deprecated: bool,

    #[serde(default)]
    pub visibility: Visibility,

    #[serde(default, flatten)]
    pub extensions: BTreeMap<String, Value>,
}

impl ImportedModule {
    /// Creates a new `ImportedModule` with the given module and default values for the other fields.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::v1::{QualifiedName, Visibility, ImportedModule};
    ///
    /// let imported_module = ImportedModule::new(QualifiedName::try_from("my.module")?);
    ///
    /// assert_eq!(imported_module.module.join(), "my.module");
    /// assert!(!imported_module.is_deprecated);
    /// assert_eq!(imported_module.visibility, Visibility::Public);
    /// assert!(imported_module.extensions.is_empty());
    /// #     Ok(())
    /// # }
    /// ```
    pub fn new(module: QualifiedName) -> Self {
        Self {
            module,
            is_deprecated: false,
            visibility: Visibility::Public,
            extensions: BTreeMap::new(),
        }
    }
}

/// An imported attribute, which is a reference to an attribute of a module that is imported in the
/// current namespace.
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct ImportedAttribute {
    pub attribute: Identifier,

    pub module: QualifiedName,

    #[serde(rename = "deprecated", default)]
    pub is_deprecated: bool,

    #[serde(default)]
    pub visibility: Visibility,

    #[serde(default, flatten)]
    pub extensions: BTreeMap<String, Value>,
}

impl ImportedAttribute {
    /// Creates a new `ImportedModuleAttribute` with the given attribute and module, and default values for the other fields.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::v1::{Identifier, QualifiedName, Visibility, ImportedAttribute};
    ///
    /// let imported_module_attribute = ImportedAttribute::new(
    ///     Identifier::try_from("my_attribute")?,
    ///     QualifiedName::try_from("my.module")?,
    /// );
    ///
    /// assert_eq!(imported_module_attribute.attribute.as_ref(), "my_attribute");
    /// assert_eq!(imported_module_attribute.module.join(), "my.module");
    /// assert!(!imported_module_attribute.is_deprecated);
    /// assert_eq!(imported_module_attribute.visibility, Visibility::Public);
    /// assert!(imported_module_attribute.extensions.is_empty());
    /// #     Ok(())
    /// # }
    /// ```
    pub fn new(attribute: Identifier, module: QualifiedName) -> Self {
        Self {
            attribute,
            module,
            is_deprecated: false,
            visibility: Visibility::Public,
            extensions: BTreeMap::new(),
        }
    }
}

/// An attribute of a module, class, or instance, which can be a function, variable, class,
/// type alias, generic, or reference to an imported module or attribute.
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum Attribute {
    #[serde(rename = "FUNCTION")]
    Function(Function),

    #[serde(rename = "VARIABLE")]
    Variable(Variable),

    #[serde(rename = "CLASS")]
    Class(Class),

    #[serde(rename = "TYPE_ALIAS")]
    TypeAlias(TypeAlias),

    #[serde(rename = "GENERIC")]
    Generic(Generic),

    #[serde(rename = "IMPORTED_MODULE")]
    ImportedModule(ImportedModule),

    #[serde(rename = "IMPORTED_ATTRIBUTE")]
    ImportedAttribute(ImportedAttribute),
}

/// The error returned when trying to convert a map of attributes into a `ModuleAttributes` struct.
#[derive(Debug, Error)]
pub enum FromModuleAttributesError {
    #[error("An attribute has a subclass visibility that should not be used in a module.")]
    ContainSubclassVisibilityAttribute {
        attributes: BTreeMap<Identifier, OneOrMany<Attribute>>,
    },
}

/// The attributes of a module, which can be functions, variables, classes, type aliases, generics,
/// or references to imported modules or attributes.
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default, Serialize)]
#[serde(transparent)]
pub struct ModuleAttributes {
    map: BTreeMap<Identifier, OneOrMany<Attribute>>,
}

impl ModuleAttributes {
    /// Creates a new `ModuleAttributes` struct with an empty map of attributes.
    pub fn new() -> Self {
        Self::default()
    }
}

impl<'de> Deserialize<'de> for ModuleAttributes {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Ok(
            ModuleAttributes::try_from(BTreeMap::deserialize(deserializer)?)
                .map_err(serde::de::Error::custom)?,
        )
    }
}

impl TryFrom<BTreeMap<Identifier, OneOrMany<Attribute>>> for ModuleAttributes {
    type Error = FromModuleAttributesError;

    /// Tries to convert a map of attributes into a `ModuleAttributes` struct, returning an error if
    /// any of the attributes have a subclass visibility that should not be used in a module.
    ///
    /// # Errors
    ///
    /// Returns `FromModuleAttributesError` if any of the attributes have a subclass visibility that
    /// should not be used in a module.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::OneOrMany;
    /// use apy::v1::{Identifier, QualifiedName, Type, Variable, Attribute, ModuleAttributes};
    /// use std::collections::BTreeMap;
    ///
    /// let attributes = BTreeMap::from([
    ///     (
    ///         Identifier::try_from("my_attribute")?,
    ///         OneOrMany::one(Attribute::Variable(Variable::new(Type::new(QualifiedName::try_from("int")?)))),
    ///     ),
    ///     (
    ///         Identifier::try_from("my_private_attribute")?,
    ///         OneOrMany::one(Attribute::Variable(Variable::new(Type::new(QualifiedName::try_from("str")?)))),
    ///     ),
    /// ]);
    ///
    /// assert!(ModuleAttributes::try_from(attributes).is_ok());
    /// #     Ok(())
    /// # }
    /// ```
    fn try_from(value: BTreeMap<Identifier, OneOrMany<Attribute>>) -> Result<Self, Self::Error> {
        let has_subclass_visibility = value.values().any(|attributes| {
            attributes.iter().any(|attribute| match attribute {
                Attribute::Function(function) => function
                    .signature
                    .iter()
                    .any(|signature| signature.visibility == Visibility::Subclass),
                Attribute::Variable(variable) => variable.visibility == Visibility::Subclass,
                Attribute::Class(class) => class.visibility == Visibility::Subclass,
                Attribute::TypeAlias(type_alias) => type_alias.visibility == Visibility::Subclass,
                Attribute::Generic(generic) => generic.visibility == Visibility::Subclass,
                Attribute::ImportedModule(imported_module) => {
                    imported_module.visibility == Visibility::Subclass
                }
                Attribute::ImportedAttribute(imported_attribute) => {
                    imported_attribute.visibility == Visibility::Subclass
                }
            })
        });

        if has_subclass_visibility {
            Err(FromModuleAttributesError::ContainSubclassVisibilityAttribute { attributes: value })
        } else {
            Ok(Self { map: value })
        }
    }
}

impl From<ModuleAttributes> for BTreeMap<Identifier, OneOrMany<Attribute>> {
    /// Unwraps the `BTreeMap<Identifier, OneOrMany<Attribute>>` from the `ModuleAttributes`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::OneOrMany;
    /// use apy::v1::{Identifier, QualifiedName, Type, Variable, Attribute, ModuleAttributes};
    /// use std::collections::BTreeMap;
    ///
    /// let module_attributes = ModuleAttributes::try_from(BTreeMap::from([
    ///     (
    ///         Identifier::try_from("my_attribute")?,
    ///         OneOrMany::one(Attribute::Variable(Variable::new(Type::new(QualifiedName::try_from("int")?)))),
    ///     ),
    ///     (
    ///         Identifier::try_from("my_private_attribute")?,
    ///         OneOrMany::one(Attribute::Variable(Variable::new(Type::new(QualifiedName::try_from("str")?)))),
    ///     ),
    /// ]))?;
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    fn from(value: ModuleAttributes) -> Self {
        value.map
    }
}

impl AsRef<BTreeMap<Identifier, OneOrMany<Attribute>>> for ModuleAttributes {
    fn as_ref(&self) -> &BTreeMap<Identifier, OneOrMany<Attribute>> {
        &self.map
    }
}

impl Deref for ModuleAttributes {
    type Target = BTreeMap<Identifier, OneOrMany<Attribute>>;

    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

/// A module, which contains all the information about a Python module.
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default, Serialize, Deserialize)]
pub struct Module {
    #[serde(default)]
    pub summary: String,

    #[serde(default)]
    pub description: String,

    #[serde(default)]
    pub raises: Vec<Exception>,

    #[serde(rename = "partial", default)]
    pub is_partial: bool,

    #[serde(default)]
    pub visibility: Visibility,

    #[serde(default)]
    pub attributes: ModuleAttributes,

    #[serde(default)]
    pub typing_attributes: ModuleAttributes,

    #[serde(default, flatten)]
    pub extensions: BTreeMap<String, Value>,
}

impl Module {
    /// Creates a new `Module` with default values for all fields.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use apy::v1::{Visibility, ModuleAttributes, Module};
    ///
    /// let module = Module::new(ModuleAttributes::new(), ModuleAttributes::new());
    ///
    /// assert!(module.summary.is_empty());
    /// assert!(module.description.is_empty());
    /// assert!(module.raises.is_empty());
    /// assert!(!module.is_partial);
    /// assert_eq!(module.visibility, Visibility::Public);
    /// assert!(module.attributes.is_empty());
    /// assert!(module.typing_attributes.is_empty());
    /// assert!(module.extensions.is_empty());
    /// ```
    pub fn new(attributes: ModuleAttributes, typing_attributes: ModuleAttributes) -> Self {
        Self {
            attributes,
            typing_attributes,
            ..Self::default()
        }
    }
}

/// The APY v1 structure, which contains all the modules.
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default, Serialize, Deserialize)]
pub struct ApyV1 {
    #[serde(default)]
    pub modules: BTreeMap<QualifiedName, Module>,

    #[serde(default, flatten)]
    pub extensions: BTreeMap<String, Value>,
}

impl ApyV1 {
    /// Creates a new `ApyV1` with an empty list of modules and extensions.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use apy::v1::ApyV1;
    ///
    /// let apy = ApyV1::new();
    ///
    /// assert!(apy.modules.is_empty());
    /// assert!(apy.extensions.is_empty());
    /// ```
    pub fn new() -> Self {
        Self::default()
    }
}
