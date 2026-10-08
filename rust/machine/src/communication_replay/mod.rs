//! Communication replay-consumption model and nullifier tracking.
use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::coroutine::Value;
use crate::session::{Edge, SessionId};
use crate::verification::{Hash, HashModel, HashTag, Nullifier};

include!("identity.rs");
include!("model.rs");
#[cfg(test)]
include!("tests.rs");
