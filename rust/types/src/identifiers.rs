//! Typed identifiers used across runtime, topology, and protocol APIs.

use std::fmt;
use std::sync::Arc;

use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IdentifierError {
    pub kind: &'static str,
    pub value: String,
}

impl fmt::Display for IdentifierError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid {} identifier: {}", self.kind, self.value)
    }
}

impl std::error::Error for IdentifierError {}

fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

fn validate_ident(kind: &'static str, value: &str) -> Result<(), IdentifierError> {
    let mut chars = value.chars();
    let Some(first) = chars.next() else {
        return Err(IdentifierError {
            kind,
            value: value.to_string(),
        });
    };
    if !is_ident_start(first) {
        return Err(IdentifierError {
            kind,
            value: value.to_string(),
        });
    }
    if !chars.all(is_ident_continue) {
        return Err(IdentifierError {
            kind,
            value: value.to_string(),
        });
    }
    Ok(())
}

macro_rules! define_ident {
    ($name:ident, $kind:literal) => {
        #[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(Arc<str>);

        impl $name {
            pub fn new(value: impl Into<String>) -> Result<Self, IdentifierError> {
                let value = value.into();
                validate_ident($kind, &value)?;
                Ok(Self(Arc::from(value)))
            }

            pub fn from_static(value: &'static str) -> Self {
                debug_assert!(validate_ident($kind, value).is_ok());
                Self(Arc::from(value))
            }

            pub fn as_str(&self) -> &str {
                &self.0
            }
        }

        impl TryFrom<String> for $name {
            type Error = IdentifierError;

            fn try_from(value: String) -> Result<Self, Self::Error> {
                Self::new(value)
            }
        }

        impl PartialEq<&str> for $name {
            fn eq(&self, other: &&str) -> bool {
                self.as_str() == *other
            }
        }

        impl PartialEq<$name> for &str {
            fn eq(&self, other: &$name) -> bool {
                *self == other.as_str()
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, concat!(stringify!($name), "({})"), self.0)
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(&self.0)
            }
        }

        impl Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                serializer.serialize_str(self.as_str())
            }
        }

        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                let value = String::deserialize(deserializer)?;
                $name::new(value).map_err(de::Error::custom)
            }
        }
    };
}

define_ident!(RoleName, "role");
define_ident!(LabelName, "label");
define_ident!(ProtocolName, "protocol");
define_ident!(Region, "region");
