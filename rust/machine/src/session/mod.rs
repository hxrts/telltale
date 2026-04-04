//! Session state, edge tracking, and verified buffer management.
use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use serde_json::Value as JsonValue;
use telltale_types::{Label, LocalTypeR, ValType};

use crate::buffer::{BoundedBuffer, BufferConfig, SignedBuffer, SignedValue};
use crate::coroutine::Value;
use crate::instr::Endpoint;
use crate::verification::{
    sign_value, signing_key_for_endpoint, verify_signed_value, verifying_key_for_endpoint,
    AuthTree, DefaultVerificationModel, Hash, HashTag, Signature, VerificationModel,
};

include!("overview.rs");
include!("state.rs");
include!("store.rs");
#[cfg(test)]
include!("tests.rs");
