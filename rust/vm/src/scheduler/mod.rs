//! Policy-based coroutine scheduler.
//!
//! All policies produce observationally equivalent results per the
//! `schedule_confluence` theorem in `lean/Runtime/Proofs/SchedulerApi.lean`.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use serde::{Deserialize, Serialize};

use crate::coroutine::BlockReason;

include!("types.rs");
include!("scheduling.rs");
#[cfg(test)]
include!("tests.rs");
