//! Sized count and length newtypes for protocol-visible values.

use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;

/// Maximum allowed role index (0-based).
pub const MAX_ROLE_INDEX: u32 = 9_999;
/// Maximum allowed loop iteration count.
pub const MAX_LOOP_COUNT: u32 = 1_000_000;
/// Maximum on-wire message length in bytes (16 MiB).
pub const MAX_MESSAGE_LEN_BYTES: u32 = 16 * 1024 * 1024;
/// Maximum queue capacity (entries).
pub const MAX_QUEUE_CAPACITY: u32 = 65_536;
/// Maximum channel capacity (bits).
pub const MAX_CHANNEL_CAPACITY_BITS: u32 = 1_024;
/// Maximum content store capacity (entries).
pub const MAX_STORE_CAPACITY: u32 = 1_000_000;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CountError {
    pub kind: &'static str,
    pub value: u64,
    pub min: u64,
    pub max: u64,
}

impl fmt::Display for CountError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "invalid {}: {} (expected {}..={})",
            self.kind, self.value, self.min, self.max
        )
    }
}

impl std::error::Error for CountError {}

macro_rules! define_count {
    ($name:ident, $doc:literal, min = $min:expr, max = $max:expr) => {
        #[doc = $doc]
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(u32);

        impl $name {
            pub const MIN: u32 = $min;
            pub const MAX: u32 = $max;

            #[must_use]
            pub fn new(value: u32) -> Self {
                assert!(
                    value >= Self::MIN,
                    concat!(stringify!($name), " below minimum")
                );
                assert!(
                    value <= Self::MAX,
                    concat!(stringify!($name), " above maximum")
                );
                Self(value)
            }

            pub fn try_new(value: u32) -> Result<Self, CountError> {
                if !(Self::MIN..=Self::MAX).contains(&value) {
                    return Err(CountError {
                        kind: stringify!($name),
                        value: value as u64,
                        min: Self::MIN as u64,
                        max: Self::MAX as u64,
                    });
                }
                Ok(Self(value))
            }

            #[must_use]
            pub const fn get(self) -> u32 {
                self.0
            }

            #[must_use]
            pub const fn as_usize(self) -> usize {
                self.0 as usize
            }
        }

        impl TryFrom<u32> for $name {
            type Error = CountError;

            fn try_from(value: u32) -> Result<Self, Self::Error> {
                Self::try_new(value)
            }
        }

        impl TryFrom<usize> for $name {
            type Error = CountError;

            fn try_from(value: usize) -> Result<Self, Self::Error> {
                let value_u32 = u32::try_from(value).map_err(|_| CountError {
                    kind: stringify!($name),
                    value: value as u64,
                    min: Self::MIN as u64,
                    max: Self::MAX as u64,
                })?;
                Self::try_new(value_u32)
            }
        }

        impl From<$name> for u32 {
            fn from(value: $name) -> Self {
                value.0
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                serializer.serialize_u32(self.0)
            }
        }

        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                let value = u32::deserialize(deserializer)?;
                $name::try_new(value).map_err(de::Error::custom)
            }
        }
    };
}

define_count!(
    RoleIndex,
    "Index for a role instance (0-based).",
    min = 0,
    max = MAX_ROLE_INDEX
);
define_count!(
    LoopCount,
    "Count of loop iterations (bounded).",
    min = 0,
    max = MAX_LOOP_COUNT
);
define_count!(
    MessageLenBytes,
    "On-wire message length in bytes.",
    min = 0,
    max = MAX_MESSAGE_LEN_BYTES
);
define_count!(
    QueueCapacity,
    "Queue capacity (entries).",
    min = 1,
    max = MAX_QUEUE_CAPACITY
);
define_count!(
    ChannelCapacity,
    "Channel capacity (bits).",
    min = 0,
    max = MAX_CHANNEL_CAPACITY_BITS
);
define_count!(
    StoreCapacity,
    "Content store capacity (entries).",
    min = 1,
    max = MAX_STORE_CAPACITY
);
