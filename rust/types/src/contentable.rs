//! Contentable Trait for Canonical Serialization
//!
//! This module provides the `Contentable` trait for types that can be
//! serialized to a canonical byte representation suitable for content addressing.
//!
//! # Design
//!
//! The serialization process:
//! 1. Convert to de Bruijn representation (for α-equivalence)
//! 2. Normalize branch ordering (deterministic)
//! 3. Serialize to bytes (JSON by default, DAG-CBOR with feature flag)
//!
//! Canonical serialization for binder-carrying protocol types requires
//! all recursion variables to be bound. Open terms are rejected.
//!
//! # Serialization Formats
//!
//! - **JSON** (default): Simple and human-readable. Uses `to_bytes`/`from_bytes`.
//! - **DAG-CBOR** (with `dag-cbor` feature): Compact binary format with a
//!   canonical CBOR backend. Uses `to_cbor_bytes`/`from_cbor_bytes`.
//!
//! # Lean Correspondence
//!
//! This module corresponds to `lean/SessionTypes/ContentIdentityPolicy.lean`.
//! The `toCbor`/`fromCbor` methods in Lean map to `to_cbor_bytes`/`from_cbor_bytes` here.

#[cfg(feature = "sha256")]
use crate::content_id::Sha256Hasher;
use crate::content_id::{Blake3Hasher, ContentId, DefaultContentHasher, Hasher};
use crate::de_bruijn::{GlobalTypeDB, LocalTypeRDB};
use crate::{GlobalType, Label, LocalTypeR, PayloadSort, MAX_MESSAGE_LEN_BYTES};
#[cfg(feature = "dag-cbor")]
use ciborium::{
    de::from_reader as cbor_from_reader,
    ser::into_writer as cbor_into_writer,
    value::{CanonicalValue, Value as CborValue},
};
use serde::{de::DeserializeOwned, Serialize};

/// Maximum accepted canonical artifact size for direct `Contentable` decodes.
pub const MAX_CONTENTABLE_BYTES: usize = MAX_MESSAGE_LEN_BYTES as usize;
/// Maximum accepted recursion depth for binder-carrying protocol artifacts.
pub const MAX_CONTENTABLE_RECURSION_DEPTH: usize = 256;

/// Trait for types with canonical serialization.
///
/// Types implementing `Contentable` can be serialized to bytes in a
/// deterministic way, enabling content addressing and structural comparison.
///
/// # Invariants
///
/// - `from_bytes(to_bytes(x)) ≈ x` (modulo α-equivalence for types with binders)
/// - Two α-equivalent values produce identical bytes
/// - Byte order is deterministic (independent of insertion order, etc.)
///
/// For binder-carrying protocol types (`GlobalType`, `LocalTypeR`), canonical
/// serialization requires all recursion variables to be bound.
///
/// # Examples
///
/// ```
/// use telltale_types::{GlobalType, Label};
/// use telltale_types::contentable::Contentable;
///
/// // α-equivalent types produce the same bytes
/// let g1 = GlobalType::mu("x", GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("x")));
/// let g2 = GlobalType::mu("y", GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("y")));
///
/// assert_eq!(g1.to_bytes().unwrap(), g2.to_bytes().unwrap());
/// ```
pub trait Contentable: Sized {
    /// Serialize to canonical byte representation (JSON format).
    ///
    /// # Errors
    ///
    /// Returns [`ContentableError`] if serialization fails.
    fn to_bytes(&self) -> Result<Vec<u8>, ContentableError>;

    /// Deserialize from JSON bytes.
    ///
    /// Callers that load bytes from a content-addressed store should prefer
    /// [`Contentable::from_bytes_verified`] so the expected content ID is checked
    /// before deserialization. Implementations must reject oversized inputs.
    ///
    /// # Errors
    ///
    /// Returns an error if deserialization fails.
    fn from_bytes(bytes: &[u8]) -> Result<Self, ContentableError>;

    /// Verify the content ID before deserializing from JSON bytes.
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes do not match `expected` or deserialization fails.
    fn from_bytes_verified<H: Hasher>(
        bytes: &[u8],
        expected: &ContentId<H>,
    ) -> Result<Self, ContentableError> {
        let actual = ContentId::<H>::from_bytes(bytes);
        if &actual != expected {
            return Err(ContentableError::InvalidFormat(format!(
                "content ID mismatch: expected {expected}, got {actual}"
            )));
        }
        Self::from_bytes(bytes)
    }

    /// Serialize to template bytes, allowing open terms with explicit
    /// free-variable interfaces when supported by the implementation.
    ///
    /// Default behavior falls back to canonical bytes.
    ///
    /// # Errors
    ///
    /// Returns [`ContentableError`] if serialization fails.
    fn to_template_bytes(&self) -> Result<Vec<u8>, ContentableError> {
        self.to_bytes()
    }

    /// Serialize to DAG-CBOR bytes (requires `dag-cbor` feature).
    ///
    /// DAG-CBOR is a deterministic subset of CBOR designed for content addressing.
    /// It produces more compact output than JSON while preserving canonical bytes.
    ///
    /// # Errors
    ///
    /// Returns [`ContentableError`] if serialization fails.
    #[cfg(feature = "dag-cbor")]
    fn to_cbor_bytes(&self) -> Result<Vec<u8>, ContentableError>;

    /// Deserialize from DAG-CBOR bytes (requires `dag-cbor` feature).
    ///
    /// # Errors
    ///
    /// Returns an error if deserialization fails.
    #[cfg(feature = "dag-cbor")]
    fn from_cbor_bytes(bytes: &[u8]) -> Result<Self, ContentableError>;

    /// Compute content ID using the specified hasher (from JSON bytes).
    ///
    /// # Errors
    ///
    /// Returns [`ContentableError`] if serialization fails.
    fn content_id<H: Hasher>(&self) -> Result<ContentId<H>, ContentableError> {
        let bytes = self.to_bytes()?;
        Ok(ContentId::from_bytes(&bytes))
    }

    /// Compute content ID using the central default content hasher (from JSON bytes).
    ///
    /// # Errors
    ///
    /// Returns [`ContentableError`] if serialization fails.
    fn content_id_default(&self) -> Result<ContentId<DefaultContentHasher>, ContentableError> {
        self.content_id()
    }

    /// Compute content ID using explicit BLAKE3 (from JSON bytes).
    ///
    /// # Errors
    ///
    /// Returns [`ContentableError`] if serialization fails.
    fn content_id_blake3(&self) -> Result<ContentId<Blake3Hasher>, ContentableError> {
        self.content_id()
    }

    /// Compute content ID using SHA-256 (from JSON bytes).
    ///
    /// # Errors
    ///
    /// Returns [`ContentableError`] if serialization fails.
    #[cfg(feature = "sha256")]
    fn content_id_sha256(&self) -> Result<ContentId<Sha256Hasher>, ContentableError> {
        self.content_id()
    }

    /// Compute a template ID using the specified hasher (from template bytes).
    ///
    /// # Errors
    ///
    /// Returns [`ContentableError`] if serialization fails.
    fn template_id<H: Hasher>(&self) -> Result<ContentId<H>, ContentableError> {
        let bytes = self.to_template_bytes()?;
        Ok(ContentId::from_bytes(&bytes))
    }

    /// Compute a template ID using the central default content hasher.
    ///
    /// # Errors
    ///
    /// Returns [`ContentableError`] if serialization fails.
    fn template_id_default(&self) -> Result<ContentId<DefaultContentHasher>, ContentableError> {
        self.template_id()
    }

    /// Compute a template ID using explicit BLAKE3.
    ///
    /// # Errors
    ///
    /// Returns [`ContentableError`] if serialization fails.
    fn template_id_blake3(&self) -> Result<ContentId<Blake3Hasher>, ContentableError> {
        self.template_id()
    }

    /// Compute a template ID using SHA-256.
    ///
    /// # Errors
    ///
    /// Returns [`ContentableError`] if serialization fails.
    #[cfg(feature = "sha256")]
    fn template_id_sha256(&self) -> Result<ContentId<Sha256Hasher>, ContentableError> {
        self.template_id()
    }

    /// Compute content ID from DAG-CBOR bytes (requires `dag-cbor` feature).
    ///
    /// This produces a different content ID than the JSON-based methods.
    /// Use this when the binary canonical encoding matters.
    ///
    /// # Errors
    ///
    /// Returns [`ContentableError`] if serialization fails.
    #[cfg(feature = "dag-cbor")]
    fn content_id_cbor<H: Hasher>(&self) -> Result<ContentId<H>, ContentableError> {
        let bytes = self.to_cbor_bytes()?;
        Ok(ContentId::from_bytes(&bytes))
    }

    /// Compute content ID from DAG-CBOR using the central default content hasher
    /// (requires `dag-cbor` feature).
    ///
    /// # Errors
    ///
    /// Returns [`ContentableError`] if serialization fails.
    #[cfg(feature = "dag-cbor")]
    fn content_id_cbor_default(&self) -> Result<ContentId<DefaultContentHasher>, ContentableError> {
        self.content_id_cbor()
    }

    /// Compute content ID from DAG-CBOR using explicit BLAKE3 (requires `dag-cbor` feature).
    ///
    /// # Errors
    ///
    /// Returns [`ContentableError`] if serialization fails.
    #[cfg(feature = "dag-cbor")]
    fn content_id_cbor_blake3(&self) -> Result<ContentId<Blake3Hasher>, ContentableError> {
        self.content_id_cbor()
    }

    /// Compute content ID from DAG-CBOR using SHA-256 (requires `dag-cbor` feature).
    ///
    /// # Errors
    ///
    /// Returns [`ContentableError`] if serialization fails.
    #[cfg(all(feature = "dag-cbor", feature = "sha256"))]
    fn content_id_cbor_sha256(&self) -> Result<ContentId<Sha256Hasher>, ContentableError> {
        self.content_id_cbor()
    }
}

/// Errors that can occur during contentable operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ContentableError {
    /// Failed to deserialize bytes
    DeserializationFailed(String),
    /// Failed to serialize value
    SerializationFailed(String),
    /// Invalid format or structure
    InvalidFormat(String),
}

impl std::fmt::Display for ContentableError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ContentableError::DeserializationFailed(msg) => {
                write!(f, "deserialization failed: {msg}")
            }
            ContentableError::SerializationFailed(msg) => {
                write!(f, "serialization failed: {msg}")
            }
            ContentableError::InvalidFormat(msg) => {
                write!(f, "invalid format: {msg}")
            }
        }
    }
}

impl std::error::Error for ContentableError {}

// Helper for JSON serialization
fn to_json_bytes<T: Serialize>(value: &T) -> Result<Vec<u8>, ContentableError> {
    // Use compact JSON without pretty printing for determinism
    serde_json::to_vec(value).map_err(|e| ContentableError::SerializationFailed(e.to_string()))
}

fn from_json_bytes<T: DeserializeOwned>(bytes: &[u8]) -> Result<T, ContentableError> {
    if bytes.len() > MAX_CONTENTABLE_BYTES {
        return Err(ContentableError::InvalidFormat(format!(
            "contentable JSON input too large: {} bytes exceeds {}",
            bytes.len(),
            MAX_CONTENTABLE_BYTES
        )));
    }
    serde_json::from_slice(bytes)
        .map_err(|e| ContentableError::DeserializationFailed(e.to_string()))
}

fn sorted_free_vars(mut vars: Vec<String>) -> Vec<String> {
    vars.sort();
    vars.dedup();
    vars
}

#[derive(Serialize)]
struct GlobalTemplateEnvelope {
    free_vars: Vec<String>,
    db: GlobalTypeDB,
}

#[derive(Serialize)]
struct LocalTemplateEnvelope {
    free_vars: Vec<String>,
    db: LocalTypeRDB,
}

// Helper for DAG-CBOR serialization (requires dag-cbor feature)
#[cfg(feature = "dag-cbor")]
fn to_cbor_bytes_impl<T: Serialize>(value: &T) -> Result<Vec<u8>, ContentableError> {
    let value = CborValue::serialized(value).map_err(|e| {
        ContentableError::SerializationFailed(format!("dag-cbor serialize value: {e}"))
    })?;
    let value = canonicalize_cbor_value(value)?;
    let mut bytes = Vec::new();
    cbor_into_writer(&value, &mut bytes)
        .map_err(|e| ContentableError::SerializationFailed(format!("dag-cbor encode: {e}")))?;
    Ok(bytes)
}

#[cfg(feature = "dag-cbor")]
fn from_cbor_bytes_impl<T: DeserializeOwned>(bytes: &[u8]) -> Result<T, ContentableError> {
    if bytes.len() > MAX_CONTENTABLE_BYTES {
        return Err(ContentableError::InvalidFormat(format!(
            "contentable CBOR input too large: {} bytes exceeds {}",
            bytes.len(),
            MAX_CONTENTABLE_BYTES
        )));
    }
    let value: CborValue = cbor_from_reader(bytes)
        .map_err(|e| ContentableError::DeserializationFailed(format!("dag-cbor decode: {e}")))?;
    let value = canonicalize_cbor_value(value)?;
    value
        .deserialized()
        .map_err(|e| ContentableError::DeserializationFailed(format!("dag-cbor: {e}")))
}

#[cfg(feature = "dag-cbor")]
fn canonicalize_cbor_value(value: CborValue) -> Result<CborValue, ContentableError> {
    match value {
        CborValue::Integer(_)
        | CborValue::Bytes(_)
        | CborValue::Float(_)
        | CborValue::Text(_)
        | CborValue::Bool(_)
        | CborValue::Null => Ok(value),
        CborValue::Tag(tag, _) => Err(ContentableError::InvalidFormat(format!(
            "unsupported DAG-CBOR tag: {tag}"
        ))),
        CborValue::Array(values) => values
            .into_iter()
            .map(canonicalize_cbor_value)
            .collect::<Result<Vec<_>, _>>()
            .map(CborValue::Array),
        CborValue::Map(entries) => canonicalize_cbor_map(entries),
        other => Err(ContentableError::InvalidFormat(format!(
            "unsupported DAG-CBOR value variant: {other:?}"
        ))),
    }
}

#[cfg(feature = "dag-cbor")]
fn canonicalize_cbor_map(
    entries: Vec<(CborValue, CborValue)>,
) -> Result<CborValue, ContentableError> {
    let mut canonical_entries = entries
        .into_iter()
        .map(|(key, value)| {
            Ok((
                canonicalize_cbor_value(key)?,
                canonicalize_cbor_value(value)?,
            ))
        })
        .collect::<Result<Vec<_>, ContentableError>>()?;

    canonical_entries.sort_by(|(left, _), (right, _)| {
        CanonicalValue::from(left.clone()).cmp(&CanonicalValue::from(right.clone()))
    });

    for pair in canonical_entries.windows(2) {
        let left = CanonicalValue::from(pair[0].0.clone());
        let right = CanonicalValue::from(pair[1].0.clone());
        if left == right {
            return Err(ContentableError::InvalidFormat(
                "DAG-CBOR map contains duplicate canonical keys".to_string(),
            ));
        }
    }

    Ok(CborValue::Map(canonical_entries))
}

// ============================================================================
// Contentable implementations
// ============================================================================

impl Contentable for PayloadSort {
    fn to_bytes(&self) -> Result<Vec<u8>, ContentableError> {
        to_json_bytes(self)
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self, ContentableError> {
        from_json_bytes(bytes)
    }

    #[cfg(feature = "dag-cbor")]
    fn to_cbor_bytes(&self) -> Result<Vec<u8>, ContentableError> {
        to_cbor_bytes_impl(self)
    }

    #[cfg(feature = "dag-cbor")]
    fn from_cbor_bytes(bytes: &[u8]) -> Result<Self, ContentableError> {
        from_cbor_bytes_impl(bytes)
    }
}

impl Contentable for Label {
    fn to_bytes(&self) -> Result<Vec<u8>, ContentableError> {
        to_json_bytes(self)
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self, ContentableError> {
        from_json_bytes(bytes)
    }

    #[cfg(feature = "dag-cbor")]
    fn to_cbor_bytes(&self) -> Result<Vec<u8>, ContentableError> {
        to_cbor_bytes_impl(self)
    }

    #[cfg(feature = "dag-cbor")]
    fn from_cbor_bytes(bytes: &[u8]) -> Result<Self, ContentableError> {
        from_cbor_bytes_impl(bytes)
    }
}

impl Contentable for GlobalType {
    fn to_bytes(&self) -> Result<Vec<u8>, ContentableError> {
        if !self.all_vars_bound() {
            return Err(ContentableError::InvalidFormat(
                "canonical serialization requires all recursion variables to be bound".to_string(),
            ));
        }
        // Convert to de Bruijn, normalize, then serialize
        let db = GlobalTypeDB::from(self).normalize();
        to_json_bytes(&db)
    }

    fn to_template_bytes(&self) -> Result<Vec<u8>, ContentableError> {
        let free_vars = sorted_free_vars(self.free_vars());
        let env: Vec<&str> = free_vars.iter().map(String::as_str).collect();
        let db = GlobalTypeDB::from_global_type_with_env(self, &env).normalize();
        let envelope = GlobalTemplateEnvelope { free_vars, db };
        to_json_bytes(&envelope)
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self, ContentableError> {
        // Note: This returns a type with generated variable names,
        // since de Bruijn indices don't preserve names.
        let db: GlobalTypeDB = from_json_bytes(bytes)?;
        global_from_de_bruijn(&db, &mut vec![], 0)
    }

    #[cfg(feature = "dag-cbor")]
    fn to_cbor_bytes(&self) -> Result<Vec<u8>, ContentableError> {
        if !self.all_vars_bound() {
            return Err(ContentableError::InvalidFormat(
                "canonical serialization requires all recursion variables to be bound".to_string(),
            ));
        }
        let db = GlobalTypeDB::from(self).normalize();
        to_cbor_bytes_impl(&db)
    }

    #[cfg(feature = "dag-cbor")]
    fn from_cbor_bytes(bytes: &[u8]) -> Result<Self, ContentableError> {
        let db: GlobalTypeDB = from_cbor_bytes_impl(bytes)?;
        global_from_de_bruijn(&db, &mut vec![], 0)
    }
}

impl Contentable for LocalTypeR {
    fn to_bytes(&self) -> Result<Vec<u8>, ContentableError> {
        if !self.all_vars_bound() {
            return Err(ContentableError::InvalidFormat(
                "canonical serialization requires all recursion variables to be bound".to_string(),
            ));
        }
        // Convert to de Bruijn, normalize, then serialize.
        // Payload annotations on local branches are preserved.
        let db = LocalTypeRDB::from(self).normalize();
        to_json_bytes(&db)
    }

    fn to_template_bytes(&self) -> Result<Vec<u8>, ContentableError> {
        let free_vars = sorted_free_vars(self.free_vars());
        let env: Vec<&str> = free_vars.iter().map(String::as_str).collect();
        let db = LocalTypeRDB::from_local_type_with_env(self, &env).normalize();
        let envelope = LocalTemplateEnvelope { free_vars, db };
        to_json_bytes(&envelope)
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self, ContentableError> {
        // Note: This returns a type with generated variable names,
        // since de Bruijn indices don't preserve names.
        let db: LocalTypeRDB = from_json_bytes(bytes)?;
        local_from_de_bruijn(&db, &mut vec![], 0)
    }

    #[cfg(feature = "dag-cbor")]
    fn to_cbor_bytes(&self) -> Result<Vec<u8>, ContentableError> {
        if !self.all_vars_bound() {
            return Err(ContentableError::InvalidFormat(
                "canonical serialization requires all recursion variables to be bound".to_string(),
            ));
        }
        let db = LocalTypeRDB::from(self).normalize();
        to_cbor_bytes_impl(&db)
    }

    #[cfg(feature = "dag-cbor")]
    fn from_cbor_bytes(bytes: &[u8]) -> Result<Self, ContentableError> {
        let db: LocalTypeRDB = from_cbor_bytes_impl(bytes)?;
        local_from_de_bruijn(&db, &mut vec![], 0)
    }
}

// ============================================================================
// De Bruijn back-conversion (generates fresh variable names)
// ============================================================================

fn check_contentable_depth(depth: usize) -> Result<(), ContentableError> {
    if depth > MAX_CONTENTABLE_RECURSION_DEPTH {
        return Err(ContentableError::InvalidFormat(format!(
            "contentable recursion depth exceeds {MAX_CONTENTABLE_RECURSION_DEPTH}"
        )));
    }
    Ok(())
}

fn global_from_de_bruijn(
    db: &GlobalTypeDB,
    names: &mut Vec<String>,
    depth: usize,
) -> Result<GlobalType, ContentableError> {
    check_contentable_depth(depth)?;
    match db {
        GlobalTypeDB::End => Ok(GlobalType::End),
        GlobalTypeDB::Comm {
            sender,
            receiver,
            branches,
        } => Ok(GlobalType::Comm {
            sender: sender.clone(),
            receiver: receiver.clone(),
            branches: branches
                .iter()
                .map(|(l, cont)| Ok((l.clone(), global_from_de_bruijn(cont, names, depth + 1)?)))
                .collect::<Result<Vec<_>, ContentableError>>()?,
        }),
        GlobalTypeDB::Rec(body) => {
            // Generate a fresh variable name
            let var_name = format!("t{}", names.len());
            names.push(var_name.clone());
            let body_converted = global_from_de_bruijn(body, names, depth + 1);
            names.pop();
            Ok(GlobalType::Mu {
                var: var_name,
                body: Box::new(body_converted?),
            })
        }
        GlobalTypeDB::Var(idx) => {
            // Look up the variable name from the environment
            let name = names
                .get(names.len().saturating_sub(1 + idx))
                .cloned()
                .unwrap_or_else(|| format!("free{idx}"));
            Ok(GlobalType::Var(name))
        }
    }
}

fn local_from_de_bruijn(
    db: &LocalTypeRDB,
    names: &mut Vec<String>,
    depth: usize,
) -> Result<LocalTypeR, ContentableError> {
    check_contentable_depth(depth)?;
    match db {
        LocalTypeRDB::End => Ok(LocalTypeR::End),
        LocalTypeRDB::Send { partner, branches } => Ok(LocalTypeR::Send {
            partner: partner.clone(),
            branches: branches
                .iter()
                .map(|(l, vt, cont)| {
                    Ok((
                        l.clone(),
                        vt.clone(),
                        local_from_de_bruijn(cont, names, depth + 1)?,
                    ))
                })
                .collect::<Result<Vec<_>, ContentableError>>()?,
        }),
        LocalTypeRDB::Recv { partner, branches } => Ok(LocalTypeR::Recv {
            partner: partner.clone(),
            branches: branches
                .iter()
                .map(|(l, vt, cont)| {
                    Ok((
                        l.clone(),
                        vt.clone(),
                        local_from_de_bruijn(cont, names, depth + 1)?,
                    ))
                })
                .collect::<Result<Vec<_>, ContentableError>>()?,
        }),
        LocalTypeRDB::Rec(body) => {
            // Generate a fresh variable name
            let var_name = format!("t{}", names.len());
            names.push(var_name.clone());
            let body_converted = local_from_de_bruijn(body, names, depth + 1);
            names.pop();
            Ok(LocalTypeR::Mu {
                var: var_name,
                body: Box::new(body_converted?),
            })
        }
        LocalTypeRDB::Var(idx) => {
            // Look up the variable name from the environment
            let name = names
                .get(names.len().saturating_sub(1 + idx))
                .cloned()
                .unwrap_or_else(|| format!("free{idx}"));
            Ok(LocalTypeR::Var(name))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_content_id_helper() {
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let cid = g.content_id_default().unwrap();
        assert_eq!(cid.algorithm(), "blake3");
    }

    #[test]
    fn from_bytes_verified_rejects_wrong_content_id() {
        let label = Label::new("msg");
        let bytes = label.to_bytes().unwrap();
        let wrong = ContentId::<Blake3Hasher>::from_bytes(b"different");
        let err = Label::from_bytes_verified(&bytes, &wrong).expect_err("wrong cid must fail");
        assert!(matches!(err, ContentableError::InvalidFormat(_)));
    }

    #[test]
    fn global_from_bytes_rejects_excessive_depth() {
        let mut db = GlobalTypeDB::End;
        for _ in 0..(MAX_CONTENTABLE_RECURSION_DEPTH + 1) {
            db = GlobalTypeDB::Rec(Box::new(db));
        }
        let bytes = to_json_bytes(&db).unwrap();
        GlobalType::from_bytes(&bytes).expect_err("deep artifact must fail");
    }

    #[test]
    fn from_bytes_rejects_oversized_input() {
        let bytes = vec![b' '; MAX_CONTENTABLE_BYTES + 1];
        let err = Label::from_bytes(&bytes).expect_err("oversized input must fail");
        assert!(matches!(err, ContentableError::InvalidFormat(_)));
    }

    #[test]
    fn test_payload_sort_roundtrip() {
        let sort = PayloadSort::prod(PayloadSort::Nat, PayloadSort::Bool);
        let bytes = sort.to_bytes().unwrap();
        let recovered = PayloadSort::from_bytes(&bytes).unwrap();
        assert_eq!(sort, recovered);
    }

    #[test]
    fn test_label_roundtrip() {
        let label = Label::with_sort("data", PayloadSort::Nat);
        let bytes = label.to_bytes().unwrap();
        let recovered = Label::from_bytes(&bytes).unwrap();
        assert_eq!(label, recovered);
    }

    #[test]
    fn test_global_type_alpha_equivalence() {
        // μx. A → B : msg. x
        let g1 = GlobalType::mu(
            "x",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("x")),
        );
        // μy. A → B : msg. y (same structure, different variable name)
        let g2 = GlobalType::mu(
            "y",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("y")),
        );

        // α-equivalent types should produce the same bytes
        assert_eq!(g1.to_bytes().unwrap(), g2.to_bytes().unwrap());

        // And the same content ID
        assert_eq!(
            g1.content_id_default().unwrap(),
            g2.content_id_default().unwrap()
        );
    }

    #[test]
    fn test_local_type_alpha_equivalence() {
        // μx. !B{msg.x}
        let t1 = LocalTypeR::mu(
            "x",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("x")),
        );
        // μy. !B{msg.y}
        let t2 = LocalTypeR::mu(
            "y",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("y")),
        );

        assert_eq!(t1.to_bytes().unwrap(), t2.to_bytes().unwrap());
        assert_eq!(
            t1.content_id_default().unwrap(),
            t2.content_id_default().unwrap()
        );
    }

    #[test]
    fn test_global_type_roundtrip() {
        let g = GlobalType::mu(
            "x",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("x")),
        );

        let bytes = g.to_bytes().unwrap();
        let recovered = GlobalType::from_bytes(&bytes).unwrap();

        // Roundtrip should be α-equivalent (same structure, possibly different names)
        assert_eq!(g.to_bytes().unwrap(), recovered.to_bytes().unwrap());
    }

    #[test]
    fn test_local_type_roundtrip() {
        let t = LocalTypeR::mu(
            "x",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("x")),
        );

        let bytes = t.to_bytes().unwrap();
        let recovered = LocalTypeR::from_bytes(&bytes).unwrap();

        assert_eq!(t.to_bytes().unwrap(), recovered.to_bytes().unwrap());
    }

    #[test]
    fn test_local_type_roundtrip_preserves_payload_annotation() {
        let t = LocalTypeR::Send {
            partner: "B".to_string(),
            branches: vec![(
                Label::new("msg"),
                Some(crate::ValType::Nat),
                LocalTypeR::Recv {
                    partner: "A".to_string(),
                    branches: vec![(
                        Label::new("ack"),
                        Some(crate::ValType::Bool),
                        LocalTypeR::End,
                    )],
                },
            )],
        };

        let bytes = t.to_bytes().unwrap();
        let recovered = LocalTypeR::from_bytes(&bytes).unwrap();
        assert_eq!(t, recovered);
    }

    #[test]
    fn test_branch_ordering_normalized() {
        // Branches in different order should produce same bytes
        let g1 = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("b"), GlobalType::End),
                (Label::new("a"), GlobalType::End),
            ],
        );
        let g2 = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("a"), GlobalType::End),
                (Label::new("b"), GlobalType::End),
            ],
        );

        assert_eq!(g1.to_bytes().unwrap(), g2.to_bytes().unwrap());
    }

    #[test]
    fn test_different_types_different_bytes() {
        let g1 = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let g2 = GlobalType::send("A", "B", Label::new("other"), GlobalType::End);

        assert_ne!(g1.to_bytes().unwrap(), g2.to_bytes().unwrap());
        assert_ne!(
            g1.content_id_default().unwrap(),
            g2.content_id_default().unwrap()
        );
    }

    #[test]
    fn test_nested_recursion_content_id() {
        // μx. μy. A → B : msg. y
        let g1 = GlobalType::mu(
            "x",
            GlobalType::mu(
                "y",
                GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("y")),
            ),
        );
        // μa. μb. A → B : msg. b
        let g2 = GlobalType::mu(
            "a",
            GlobalType::mu(
                "b",
                GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("b")),
            ),
        );

        assert_eq!(
            g1.content_id_default().unwrap(),
            g2.content_id_default().unwrap()
        );
    }

    #[test]
    fn test_different_binder_reference() {
        // μx. μy. A → B : msg. x (references OUTER binder)
        let g1 = GlobalType::mu(
            "x",
            GlobalType::mu(
                "y",
                GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("x")),
            ),
        );
        // μx. μy. A → B : msg. y (references INNER binder)
        let g2 = GlobalType::mu(
            "x",
            GlobalType::mu(
                "y",
                GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("y")),
            ),
        );

        // These are NOT α-equivalent
        assert_ne!(
            g1.content_id_default().unwrap(),
            g2.content_id_default().unwrap()
        );
    }

    #[test]
    fn test_global_type_open_term_rejected_for_canonical_serialization() {
        let open = GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("free_t"));
        let err = open.to_bytes().expect_err("open terms must be rejected");
        assert!(matches!(err, ContentableError::InvalidFormat(_)));
    }

    #[test]
    fn test_local_type_open_term_rejected_for_canonical_serialization() {
        let open = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("free_t"));
        let err = open.to_bytes().expect_err("open terms must be rejected");
        assert!(matches!(err, ContentableError::InvalidFormat(_)));
    }

    #[test]
    fn test_global_type_open_term_has_template_id() {
        let open = GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("free_t"));
        let tid = open
            .template_id_default()
            .expect("open terms should support template IDs");
        let tid2 = open
            .template_id_default()
            .expect("template IDs should be deterministic");
        assert_eq!(tid, tid2);
    }

    #[test]
    fn test_local_type_open_term_has_template_id() {
        let open = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("free_t"));
        let tid = open
            .template_id_default()
            .expect("open terms should support template IDs");
        let tid2 = open
            .template_id_default()
            .expect("template IDs should be deterministic");
        assert_eq!(tid, tid2);
    }

    #[test]
    fn test_template_id_distinguishes_free_variable_interfaces() {
        let g1 = GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("x"));
        let g2 = GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("y"));
        assert_ne!(
            g1.template_id_default().unwrap(),
            g2.template_id_default().unwrap()
        );
    }

    // ========================================================================
    // DAG-CBOR tests (require dag-cbor feature)
    // ========================================================================

    #[cfg(feature = "dag-cbor")]
    mod cbor_tests {
        use super::*;

        #[test]
        fn test_payload_sort_cbor_roundtrip() {
            let sort = PayloadSort::prod(PayloadSort::Nat, PayloadSort::Bool);
            let bytes = sort.to_cbor_bytes().unwrap();
            let recovered = PayloadSort::from_cbor_bytes(&bytes).unwrap();
            assert_eq!(sort, recovered);
        }

        #[test]
        fn test_label_cbor_roundtrip() {
            let label = Label::with_sort("data", PayloadSort::Nat);
            let bytes = label.to_cbor_bytes().unwrap();
            let recovered = Label::from_cbor_bytes(&bytes).unwrap();
            assert_eq!(label, recovered);
        }

        #[test]
        fn test_global_type_cbor_roundtrip() {
            let g = GlobalType::mu(
                "x",
                GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("x")),
            );

            let bytes = g.to_cbor_bytes().unwrap();
            let recovered = GlobalType::from_cbor_bytes(&bytes).unwrap();

            // Roundtrip should be α-equivalent
            assert_eq!(
                g.to_cbor_bytes().unwrap(),
                recovered.to_cbor_bytes().unwrap()
            );
        }

        #[test]
        fn test_local_type_cbor_roundtrip() {
            let t = LocalTypeR::mu(
                "x",
                LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("x")),
            );

            let bytes = t.to_cbor_bytes().unwrap();
            let recovered = LocalTypeR::from_cbor_bytes(&bytes).unwrap();

            assert_eq!(
                t.to_cbor_bytes().unwrap(),
                recovered.to_cbor_bytes().unwrap()
            );
        }

        #[test]
        fn test_cbor_alpha_equivalence() {
            // Two α-equivalent types should produce the same CBOR bytes
            let g1 = GlobalType::mu(
                "x",
                GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("x")),
            );
            let g2 = GlobalType::mu(
                "y",
                GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("y")),
            );

            assert_eq!(g1.to_cbor_bytes().unwrap(), g2.to_cbor_bytes().unwrap());
            assert_eq!(
                g1.content_id_cbor_default().unwrap(),
                g2.content_id_cbor_default().unwrap()
            );
        }

        #[test]
        fn test_cbor_more_compact_than_json() {
            // CBOR should typically be more compact than JSON
            let g = GlobalType::comm(
                "A",
                "B",
                vec![
                    (Label::new("msg1"), GlobalType::End),
                    (Label::new("msg2"), GlobalType::End),
                    (Label::new("msg3"), GlobalType::End),
                ],
            );

            let json_bytes = g.to_bytes().unwrap();
            let cbor_bytes = g.to_cbor_bytes().unwrap();

            // CBOR is typically 30-50% smaller than JSON for structured data
            assert!(
                cbor_bytes.len() < json_bytes.len(),
                "CBOR ({} bytes) should be smaller than JSON ({} bytes)",
                cbor_bytes.len(),
                json_bytes.len()
            );
        }

        #[test]
        fn test_json_and_cbor_produce_different_bytes() {
            // JSON and CBOR are different formats, so bytes should differ
            let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

            let json_bytes = g.to_bytes().unwrap();
            let cbor_bytes = g.to_cbor_bytes().unwrap();

            assert_ne!(json_bytes, cbor_bytes);
        }
    }
}

// ============================================================================
// Property-based tests for α-equivalence
// ============================================================================

#[cfg(test)]
mod proptests {
    use super::*;
    use proptest::prelude::*;

    /// Generate a random variable name from a small set
    fn arb_var_name() -> impl Strategy<Value = String> {
        prop_oneof![
            Just("x".to_string()),
            Just("y".to_string()),
            Just("z".to_string()),
            Just("t".to_string()),
            Just("s".to_string()),
        ]
    }

    /// Generate a random role name
    fn arb_role() -> impl Strategy<Value = String> {
        prop_oneof![
            Just("A".to_string()),
            Just("B".to_string()),
            Just("C".to_string()),
        ]
    }

    /// Generate a random label
    fn arb_label() -> impl Strategy<Value = Label> {
        prop_oneof![
            Just(Label::new("msg")),
            Just(Label::new("data")),
            Just(Label::new("ack")),
            Just(Label::with_sort("value", PayloadSort::Nat)),
            Just(Label::with_sort("flag", PayloadSort::Bool)),
        ]
    }

    /// Generate a random LocalTypeR (limited depth)
    #[allow(dead_code)]
    fn arb_local_type(depth: usize) -> impl Strategy<Value = LocalTypeR> {
        if depth == 0 {
            prop_oneof![
                Just(LocalTypeR::End),
                arb_var_name().prop_map(LocalTypeR::var),
            ]
            .boxed()
        } else {
            prop_oneof![
                Just(LocalTypeR::End),
                // Simple send
                (arb_role(), arb_label(), arb_local_type(depth - 1))
                    .prop_map(|(partner, label, cont)| LocalTypeR::send(partner, label, cont)),
                // Simple recv
                (arb_role(), arb_label(), arb_local_type(depth - 1))
                    .prop_map(|(partner, label, cont)| LocalTypeR::recv(partner, label, cont)),
                // Recursive type
                (arb_var_name(), arb_local_type(depth - 1))
                    .prop_map(|(var, body)| LocalTypeR::mu(var, body)),
                // Variable
                arb_var_name().prop_map(LocalTypeR::var),
            ]
            .boxed()
        }
    }

    /// Rename all bound variables in a GlobalType using a mapping
    fn rename_global_type(g: &GlobalType, mapping: &[(&str, &str)]) -> GlobalType {
        fn rename_inner(
            g: &GlobalType,
            mapping: &[(&str, &str)],
            bound: &mut Vec<(String, String)>,
        ) -> GlobalType {
            match g {
                GlobalType::End => GlobalType::End,
                GlobalType::Comm {
                    sender,
                    receiver,
                    branches,
                } => GlobalType::Comm {
                    sender: sender.clone(),
                    receiver: receiver.clone(),
                    branches: branches
                        .iter()
                        .map(|(l, cont)| (l.clone(), rename_inner(cont, mapping, bound)))
                        .collect(),
                },
                GlobalType::Mu { var, body } => {
                    // Find new name for this variable
                    let new_var = mapping
                        .iter()
                        .find(|(old, _)| *old == var)
                        .map(|(_, new)| (*new).to_string())
                        .unwrap_or_else(|| var.clone());

                    bound.push((var.clone(), new_var.clone()));
                    let new_body = rename_inner(body, mapping, bound);
                    bound.pop();

                    GlobalType::Mu {
                        var: new_var,
                        body: Box::new(new_body),
                    }
                }
                GlobalType::Var(name) => {
                    // Check if this is a bound variable that was renamed
                    let new_name = bound
                        .iter()
                        .rev()
                        .find(|(old, _)| old == name)
                        .map(|(_, new)| new.clone())
                        .unwrap_or_else(|| name.clone());
                    GlobalType::Var(new_name)
                }
            }
        }
        rename_inner(g, mapping, &mut vec![])
    }

    /// Generate a CLOSED global type (no free variables)
    /// Uses a fixed variable name to ensure the body only references the bound var
    fn arb_closed_global_type(depth: usize) -> impl Strategy<Value = GlobalType> {
        // Use a fixed variable name for the binder
        arb_var_name().prop_flat_map(move |var| {
            let var_clone = var.clone();
            arb_global_type_closed_body(depth, var)
                .prop_map(move |body| GlobalType::mu(var_clone.clone(), body))
        })
    }

    /// Generate a global type body that only references the given bound variable
    fn arb_global_type_closed_body(
        depth: usize,
        bound_var: String,
    ) -> impl Strategy<Value = GlobalType> {
        if depth == 0 {
            prop_oneof![
                Just(GlobalType::End),
                Just(GlobalType::var(bound_var)), // Reference the bound variable
            ]
            .boxed()
        } else {
            let bv = bound_var.clone();
            let bv2 = bound_var.clone();
            prop_oneof![
                Just(GlobalType::End),
                Just(GlobalType::var(bv)),
                // Simple send
                (arb_role(), arb_role(), arb_label()).prop_flat_map(
                    move |(sender, receiver, label)| {
                        let bv_inner = bv2.clone();
                        arb_global_type_closed_body(depth - 1, bv_inner).prop_map(move |cont| {
                            GlobalType::send(sender.clone(), receiver.clone(), label.clone(), cont)
                        })
                    }
                ),
            ]
            .boxed()
        }
    }

    proptest! {
        /// Property: Same type produces same content ID
        #[test]
        fn prop_content_id_deterministic(g in arb_closed_global_type(3)) {
            let cid1 = g.content_id_default().unwrap();
            let cid2 = g.content_id_default().unwrap();
            prop_assert_eq!(cid1, cid2);
        }

        /// Property: Same type produces same bytes
        #[test]
        fn prop_to_bytes_deterministic(g in arb_closed_global_type(3)) {
            let bytes1 = g.to_bytes().unwrap();
            let bytes2 = g.to_bytes().unwrap();
            prop_assert_eq!(bytes1, bytes2);
        }

        /// Property: α-equivalent CLOSED types produce same content ID
        /// (Free variables are NOT subject to α-equivalence)
        #[test]
        fn prop_alpha_equivalence_closed(g in arb_closed_global_type(3)) {
            // Rename bound variable x → y throughout the type
            let renamed = rename_global_type(&g, &[("x", "renamed_x"), ("y", "renamed_y"), ("t", "renamed_t")]);

            // α-equivalent closed types should have same content ID
            prop_assert_eq!(
                g.content_id_default().unwrap(),
                renamed.content_id_default().unwrap(),
                "α-equivalent closed types should have same content ID"
            );
        }

        /// Property: roundtrip preserves content ID for well-formed types
        #[test]
        fn prop_roundtrip_closed(g in arb_closed_global_type(3)) {
            let bytes = g.to_bytes().unwrap();
            if let Ok(recovered) = GlobalType::from_bytes(&bytes) {
                // Roundtrip should preserve content ID (α-equivalence)
                prop_assert_eq!(
                    g.content_id_default().unwrap(),
                    recovered.content_id_default().unwrap(),
                    "roundtrip should preserve content ID for closed types"
                );
            }
        }

        /// Property: branch order doesn't affect content ID
        #[test]
        fn prop_branch_order_invariant(
            sender in arb_role(),
            receiver in arb_role(),
            label1 in arb_label(),
            label2 in arb_label(),
        ) {
            // Different label order
            let g1 = GlobalType::comm(
                &sender, &receiver,
                vec![
                    (label1.clone(), GlobalType::End),
                    (label2.clone(), GlobalType::End),
                ],
            );
            let g2 = GlobalType::comm(
                &sender, &receiver,
                vec![
                    (label2, GlobalType::End),
                    (label1, GlobalType::End),
                ],
            );

            // Same content ID regardless of branch order
            prop_assert_eq!(
                g1.content_id_default().unwrap(),
                g2.content_id_default().unwrap(),
                "branch order should not affect content ID"
            );
        }

        /// Property: LocalTypeR α-equivalence
        #[test]
        fn prop_local_type_alpha_equiv(
            partner in arb_role(),
            label in arb_label(),
        ) {
            let t1 = LocalTypeR::mu("x", LocalTypeR::send(&partner, label.clone(), LocalTypeR::var("x")));
            let t2 = LocalTypeR::mu("y", LocalTypeR::send(&partner, label, LocalTypeR::var("y")));

            prop_assert_eq!(
                t1.content_id_default().unwrap(),
                t2.content_id_default().unwrap(),
                "α-equivalent local types should have same content ID"
            );
        }
    }
}
