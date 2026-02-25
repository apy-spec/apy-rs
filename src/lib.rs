//! A Rust library for working with the APY specification format, providing data structures and
//! serialization/deserialization capabilities for different versions of APY.
use serde::{Deserialize, Serialize};
pub use serde_json::{Map, Value};
#[cfg(feature = "yaml")]
use serde_saphyr;
use std::ops::Deref;
use thiserror::Error;
#[cfg(feature = "schemars")]
use {
    schemars::{JsonSchema, Schema, SchemaGenerator, json_schema},
    std::borrow::Cow,
};

/// A helper function to provide a default value of `true` for serde deserialization.
pub(crate) fn default_true() -> bool {
    true
}

const EXPECT_SELF_NON_EMPTY_MESSAGE: &str = "Self should never be empty";

/// An error indicating that an attempt was made to convert an empty iterator into a `OneOrMany` instance.
#[derive(Debug, Error)]
#[error("Tried to convert an empty iterator")]
pub struct FromEmptyIteratorError;

/// A wrapper type that can hold either a single value of type `T` or multiple values of type `T`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct OneOrMany<T> {
    // Invariant: elements should never be empty
    elements: Vec<T>,
}

impl<T> OneOrMany<T> {
    /// Creates a new `OneOrMany` instance containing a single value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::OneOrMany;
    ///
    /// let single = OneOrMany::one(42);
    ///
    /// assert_eq!(single.first(), &42);
    /// assert_eq!(single.last(), &42);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn one(value: T) -> Self {
        Self {
            elements: vec![value],
        }
    }

    /// Attempts to create a new `OneOrMany` instance from an iterator. Returns an error if the iterator is empty.
    ///
    /// # Errors
    ///
    /// Returns a `FromEmptyIteratorError` if the provided iterator is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::OneOrMany;
    ///
    /// let many = OneOrMany::try_from_iter([1, 2, 3])?;
    ///
    /// assert_eq!(many.first(), &1);
    /// assert_eq!(many.last(), &3);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn try_from_iter<I: IntoIterator<Item = T>>(
        iter: I,
    ) -> Result<Self, FromEmptyIteratorError> {
        Self::try_from(Vec::from_iter(iter))
    }

    /// Returns a reference to the first element in the `OneOrMany` instance.
    pub fn first(&self) -> &T {
        self.elements.first().expect(EXPECT_SELF_NON_EMPTY_MESSAGE)
    }

    /// Returns a reference to the last element in the `OneOrMany` instance.
    pub fn last(&self) -> &T {
        self.elements.last().expect(EXPECT_SELF_NON_EMPTY_MESSAGE)
    }

    /// Returns the number of elements in the `OneOrMany` instance.
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// Adds a value to the `OneOrMany` instance.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::OneOrMany;
    ///
    /// let mut many = OneOrMany::one(1);
    /// many.push(2);
    ///
    /// assert_eq!(many.as_ref(), [1, 2]);
    /// #     Ok(())
    /// # }
    /// ```
    pub fn push(&mut self, value: T) {
        self.elements.push(value);
    }

    /// Extends the `OneOrMany` instance with values from an iterator.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::OneOrMany;
    ///
    /// let mut many = OneOrMany::one(1);
    /// many.extend([2, 3]);
    ///
    /// assert_eq!(many.as_ref(), [1, 2, 3]);
    /// #     Ok(())
    /// # }
    /// ```
    pub fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.elements.extend(iter);
    }

    /// Removes the last element from the `OneOrMany` instance and returns it, if there is
    /// more than one element. Returns `None` if there is only one element.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::OneOrMany;
    ///
    /// let mut many = OneOrMany::try_from(vec![1, 2, 3])?;
    ///
    /// assert_eq!(many.pop(), Some(3));
    /// assert_eq!(many.as_ref(), [1, 2]);
    /// #     Ok(())
    /// # }
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        if self.elements.len() == 1 {
            None
        } else {
            self.elements.pop()
        }
    }
}

impl<T: Serialize> Serialize for OneOrMany<T> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if self.elements.len() == 1 {
            self.first().serialize(serializer)
        } else {
            self.elements.serialize(serializer)
        }
    }
}

impl<'de, T: Deserialize<'de>> Deserialize<'de> for OneOrMany<T> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct OneOrManyVisitor<T>(std::marker::PhantomData<T>);

        impl<'de, T: Deserialize<'de>> serde::de::Visitor<'de> for OneOrManyVisitor<T> {
            type Value = OneOrMany<T>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("a single value or an array of values")
            }

            fn visit_seq<A: serde::de::SeqAccess<'de>>(
                self,
                mut seq: A,
            ) -> Result<Self::Value, A::Error> {
                let mut elements: Vec<T> = Vec::with_capacity(seq.size_hint().unwrap_or(0));
                while let Some(value) = seq.next_element()? {
                    elements.push(value);
                }
                OneOrMany::try_from(elements).map_err(serde::de::Error::custom)
            }

            fn visit_map<A: serde::de::MapAccess<'de>>(
                self,
                map: A,
            ) -> Result<Self::Value, A::Error> {
                Ok(OneOrMany::one(T::deserialize(
                    serde::de::value::MapAccessDeserializer::new(map),
                )?))
            }
        }

        deserializer.deserialize_any(OneOrManyVisitor(std::marker::PhantomData))
    }
}

#[cfg(feature = "schemars")]
impl<T: JsonSchema> JsonSchema for OneOrMany<T> {
    fn schema_name() -> Cow<'static, str> {
        Cow::Owned(format!("OneOrMany{}", T::schema_name()))
    }

    fn schema_id() -> Cow<'static, str> {
        Cow::Owned(format!("{}::OneOrMany({})", module_path!(), T::schema_id()))
    }

    fn json_schema(generator: &mut SchemaGenerator) -> Schema {
        let element_schema = generator.subschema_for::<T>();

        json_schema!({
            "anyOf": [
                element_schema,
                {
                    "type": "array",
                    "items": element_schema,
                    "minItems": 1,
                }
            ]
        })
    }
}

impl<T> From<T> for OneOrMany<T> {
    /// Converts a single value of type `T` into a `OneOrMany<T>` instance containing that value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::OneOrMany;
    ///
    /// let single = OneOrMany::from(42);
    ///
    /// assert_eq!(single.first(), &42);
    /// assert_eq!(single.last(), &42);
    /// #     Ok(())
    /// # }
    fn from(value: T) -> Self {
        Self::one(value)
    }
}

impl<T> TryFrom<Vec<T>> for OneOrMany<T> {
    type Error = FromEmptyIteratorError;

    /// Attempts to convert a `Vec<T>` into a `OneOrMany<T>` instance. Returns an error if the vector is empty.
    ///
    /// # Errors
    ///
    /// Returns a `FromEmptyIteratorError` if the provided vector is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::OneOrMany;
    ///
    /// let many: OneOrMany<u32> = OneOrMany::try_from(vec![1, 2, 3])?;
    ///
    /// assert_eq!(many.first(), &1);
    /// assert_eq!(many.last(), &3);
    /// #     Ok(())
    /// # }
    /// ```
    fn try_from(value: Vec<T>) -> Result<Self, Self::Error> {
        if value.is_empty() {
            Err(FromEmptyIteratorError)
        } else {
            Ok(Self { elements: value })
        }
    }
}

impl<T> From<OneOrMany<T>> for Vec<T> {
    /// Unwraps the `Vec<T>` from the `OneOrMany<T>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use apy::OneOrMany;
    ///
    /// let many = OneOrMany::try_from(vec![1, 2, 3])?;
    /// let vec: Vec<u32> = Vec::from(many);
    ///
    /// assert_eq!(vec, vec![1, 2, 3]);
    /// #     Ok(())
    /// # }
    /// ```
    fn from(one_or_many: OneOrMany<T>) -> Self {
        one_or_many.elements
    }
}

impl<T> AsRef<[T]> for OneOrMany<T> {
    fn as_ref(&self) -> &[T] {
        &self.elements
    }
}

impl<T> Deref for OneOrMany<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.elements
    }
}

impl<T> IntoIterator for OneOrMany<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.elements.into_iter()
    }
}

pub mod v1;

#[derive(Debug, Serialize, Deserialize, Error)]
#[error("Failed to parse APY: {0}")]
pub struct ParseApyError(String);

impl From<serde_json::Error> for ParseApyError {
    fn from(error: serde_json::Error) -> Self {
        ParseApyError(error.to_string())
    }
}

#[cfg(feature = "yaml")]
impl From<serde_saphyr::Error> for ParseApyError {
    fn from(error: serde_saphyr::Error) -> Self {
        ParseApyError(error.to_string())
    }
}

/// The main APY structure, which can represent the different versions of the APY format.
#[cfg_attr(feature = "schemars", derive(JsonSchema))]
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[serde(tag = "apy")]
#[non_exhaustive]
pub enum Apy {
    #[serde(rename = "1.0.0")]
    V1(v1::ApyV1),
}

impl Apy {
    /// Parses an `Apy` from a JSON string.
    ///
    /// # Errors
    ///
    /// Returns a `ParseApyError` if the provided string is not valid JSON or does not conform to the expected APY structure.
    pub fn from_json_str(json_str: &str) -> Result<Self, ParseApyError> {
        serde_json::from_str(json_str)?
    }

    /// Parses an `Apy` from a reader containing JSON data.
    ///
    /// # Errors
    ///
    /// Returns a `ParseApyError` if the provided reader contains invalid JSON or does not conform to the expected APY structure.
    pub fn from_json_reader(reader: impl std::io::Read) -> Result<Self, ParseApyError> {
        serde_json::from_reader(reader)?
    }

    /// Parses an `Apy` from a YAML string.
    ///
    /// # Errors
    ///
    /// Returns a `ParseApyError` if the provided string is not valid YAML or does not conform to the expected APY structure.
    #[cfg(feature = "yaml")]
    pub fn from_yaml_str(yaml_str: &str) -> Result<Self, ParseApyError> {
        serde_saphyr::from_str(yaml_str)?
    }

    /// Parses an `Apy` from a reader containing YAML data.
    ///
    /// # Errors
    ///
    /// Returns a `ParseApyError` if the provided reader contains invalid YAML or does not conform to the expected APY structure.
    #[cfg(feature = "yaml")]
    pub fn from_yaml_reader(reader: impl std::io::Read) -> Result<Self, ParseApyError> {
        serde_saphyr::from_reader(reader)?
    }

    /// Returns the version of the APY format represented by this `Apy` instance.
    pub fn version(&self) -> &str {
        match self {
            Apy::V1(_) => "1.0.0",
        }
    }
}
