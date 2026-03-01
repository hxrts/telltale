//! Typed protocol annotations
//!
//! This module provides a type-safe representation for protocol annotations,
//! replacing raw string key-value pairs with structured variants.
//!
//! # Design Philosophy
//!
//! Known annotation types (like `TimedChoice`) get dedicated variants with
//! proper types (e.g., `Duration` instead of milliseconds as string).
//! Unknown/custom annotations use the `Custom` fallback variant.
//!
//! This approach:
//! - Provides type safety for known annotations
//! - Enables pattern matching in code generation
//! - Preserves extensibility for future annotation types
//! - Maintains backward compatibility via `Custom` variant

use std::time::Duration;

#[path = "annotation_collection.rs"]
mod collection;

pub use collection::Annotations;

/// A typed annotation on a protocol statement.
///
/// Annotations provide metadata that affects code generation or runtime behavior
/// without changing the core session type semantics.
#[derive(Debug, Clone, PartialEq)]
pub enum ProtocolAnnotation {
    /// Timed choice: race an operation against a timeout.
    ///
    /// When applied to a `Choice`, the choosing role races the operation
    /// against the specified duration. If timeout fires first, takes
    /// the `TimedOut` branch; otherwise takes the `OnTime` branch.
    TimedChoice {
        /// Maximum time to wait before timing out.
        duration: Duration,
    },

    /// Priority hint for scheduling.
    ///
    /// Higher values indicate higher priority. Implementation-specific.
    Priority(u32),

    /// Retry count for transient failures.
    ///
    /// Indicates how many times to retry the operation before failing.
    Retry {
        /// Maximum retry attempts.
        max_attempts: u32,
        /// Optional delay between retries.
        delay: Option<Duration>,
    },

    /// Mark a statement as idempotent (safe to retry).
    Idempotent,

    /// Trace/debug annotation for logging.
    Trace {
        /// Optional trace label for identification.
        label: Option<String>,
    },

    /// Runtime timeout hint (for transport layer, not session type).
    ///
    /// Unlike `TimedChoice`, this doesn't affect the session type - it's
    /// purely a hint to the transport layer.
    RuntimeTimeout(Duration),

    /// Heartbeat pattern: sender sends periodic heartbeats, receiver detects absence.
    ///
    /// Desugars to a recursive choice where receiver decides liveness.
    /// The runtime uses `interval` for heartbeat timing and `on_missing_count`
    /// to determine when to declare the sender dead.
    Heartbeat {
        /// Interval between heartbeats.
        interval: Duration,
        /// Number of missing heartbeats before declaring dead.
        on_missing_count: u32,
    },

    /// Execute broadcast/collect operations in parallel.
    ///
    /// When applied to a message with a wildcard/range destination,
    /// sends or receives are executed concurrently rather than sequentially.
    Parallel,

    /// Preserve strict message ordering.
    ///
    /// When applied to a collect operation, messages are returned in the
    /// order specified by the role list. This is the default behavior
    /// for sequential collect.
    Ordered,

    /// Minimum number of responses required for a collect operation.
    ///
    /// When applied to a collect with wildcard/range source, the operation
    /// succeeds once at least `min` responses are received. Remaining responses
    /// are discarded or handled asynchronously.
    MinResponses(u32),

    /// Custom annotation for extensions or unknown types.
    ///
    /// Falls back to key-value string pairs for extensibility.
    Custom {
        /// The annotation key.
        key: String,
        /// The annotation value.
        value: String,
    },
}

impl ProtocolAnnotation {
    fn custom_legacy(key: &str, value: &str) -> Self {
        Self::Custom {
            key: key.to_string(),
            value: value.to_string(),
        }
    }

    fn parse_u32_legacy(value: &str) -> Option<u32> {
        value.parse::<u32>().ok()
    }

    fn parse_u64_legacy(value: &str) -> Option<u64> {
        value.parse::<u64>().ok()
    }

    /// Create a timed choice annotation from a duration.
    #[must_use]
    pub fn timed_choice(duration: Duration) -> Self {
        Self::TimedChoice { duration }
    }

    /// Create a timed choice annotation from milliseconds.
    #[must_use]
    pub fn timed_choice_ms(ms: u64) -> Self {
        Self::TimedChoice {
            duration: Duration::from_millis(ms),
        }
    }

    /// Create a priority annotation.
    #[must_use]
    pub fn priority(value: u32) -> Self {
        Self::Priority(value)
    }

    /// Create a retry annotation with just max attempts.
    #[must_use]
    pub fn retry(max_attempts: u32) -> Self {
        Self::Retry {
            max_attempts,
            delay: None,
        }
    }

    /// Create a retry annotation with delay between attempts.
    #[must_use]
    pub fn retry_with_delay(max_attempts: u32, delay: Duration) -> Self {
        Self::Retry {
            max_attempts,
            delay: Some(delay),
        }
    }

    /// Create a trace annotation without a label.
    #[must_use]
    pub fn trace() -> Self {
        Self::Trace { label: None }
    }

    /// Create a trace annotation with a label.
    #[must_use]
    pub fn trace_labeled(label: impl Into<String>) -> Self {
        Self::Trace {
            label: Some(label.into()),
        }
    }

    /// Create a runtime timeout annotation.
    #[must_use]
    pub fn runtime_timeout(duration: Duration) -> Self {
        Self::RuntimeTimeout(duration)
    }

    /// Create a heartbeat annotation from a duration and missing count.
    #[must_use]
    pub fn heartbeat(interval: Duration, on_missing_count: u32) -> Self {
        Self::Heartbeat {
            interval,
            on_missing_count,
        }
    }

    /// Create a heartbeat annotation from milliseconds and missing count.
    #[must_use]
    pub fn heartbeat_ms(interval_ms: u64, on_missing_count: u32) -> Self {
        Self::Heartbeat {
            interval: Duration::from_millis(interval_ms),
            on_missing_count,
        }
    }

    /// Create a parallel annotation.
    #[must_use]
    pub fn parallel() -> Self {
        Self::Parallel
    }

    /// Create an ordered annotation.
    #[must_use]
    pub fn ordered() -> Self {
        Self::Ordered
    }

    /// Create a min_responses annotation.
    #[must_use]
    pub fn min_responses(min: u32) -> Self {
        Self::MinResponses(min)
    }

    /// Create a custom annotation.
    #[must_use]
    pub fn custom(key: impl Into<String>, value: impl Into<String>) -> Self {
        Self::Custom {
            key: key.into(),
            value: value.into(),
        }
    }

    /// Check if this is a timed choice annotation.
    #[must_use]
    pub fn is_timed_choice(&self) -> bool {
        matches!(self, Self::TimedChoice { .. })
    }

    /// Get the timed choice duration, if this is a timed choice.
    #[must_use]
    pub fn timed_choice_duration(&self) -> Option<Duration> {
        match self {
            Self::TimedChoice { duration } => Some(*duration),
            _ => None,
        }
    }

    /// Check if this is a priority annotation.
    #[must_use]
    pub fn is_priority(&self) -> bool {
        matches!(self, Self::Priority(_))
    }

    /// Get the priority value, if this is a priority annotation.
    #[must_use]
    pub fn priority_value(&self) -> Option<u32> {
        match self {
            Self::Priority(v) => Some(*v),
            _ => None,
        }
    }

    /// Check if this is a retry annotation.
    #[must_use]
    pub fn is_retry(&self) -> bool {
        matches!(self, Self::Retry { .. })
    }

    /// Check if this is an idempotent annotation.
    #[must_use]
    pub fn is_idempotent(&self) -> bool {
        matches!(self, Self::Idempotent)
    }

    /// Check if this is a trace annotation.
    #[must_use]
    pub fn is_trace(&self) -> bool {
        matches!(self, Self::Trace { .. })
    }

    /// Check if this is a heartbeat annotation.
    #[must_use]
    pub fn is_heartbeat(&self) -> bool {
        matches!(self, Self::Heartbeat { .. })
    }

    /// Get the heartbeat parameters, if this is a heartbeat annotation.
    #[must_use]
    pub fn heartbeat_params(&self) -> Option<(Duration, u32)> {
        match self {
            Self::Heartbeat {
                interval,
                on_missing_count,
            } => Some((*interval, *on_missing_count)),
            _ => None,
        }
    }

    /// Check if this is a runtime timeout annotation.
    #[must_use]
    pub fn is_runtime_timeout(&self) -> bool {
        matches!(self, Self::RuntimeTimeout(_))
    }

    /// Get the runtime timeout duration, if this is a runtime timeout annotation.
    #[must_use]
    pub fn runtime_timeout_duration(&self) -> Option<Duration> {
        match self {
            Self::RuntimeTimeout(d) => Some(*d),
            _ => None,
        }
    }

    /// Check if this is a parallel annotation.
    #[must_use]
    pub fn is_parallel(&self) -> bool {
        matches!(self, Self::Parallel)
    }

    /// Check if this is an ordered annotation.
    #[must_use]
    pub fn is_ordered(&self) -> bool {
        matches!(self, Self::Ordered)
    }

    /// Check if this is a min_responses annotation.
    #[must_use]
    pub fn is_min_responses(&self) -> bool {
        matches!(self, Self::MinResponses(_))
    }

    /// Get the min_responses value, if this is a min_responses annotation.
    #[must_use]
    pub fn min_responses_value(&self) -> Option<u32> {
        match self {
            Self::MinResponses(n) => Some(*n),
            _ => None,
        }
    }

    /// Check if this is a custom annotation with the given key.
    #[must_use]
    pub fn is_custom_key(&self, expected_key: &str) -> bool {
        matches!(self, Self::Custom { key, .. } if key == expected_key)
    }

    /// Get the custom value if this is a custom annotation with the given key.
    #[must_use]
    pub fn custom_value(&self, expected_key: &str) -> Option<&str> {
        match self {
            Self::Custom { key, value } if key == expected_key => Some(value),
            _ => None,
        }
    }

    /// Get the annotation key (for compatibility with string-based lookups).
    #[must_use]
    pub fn key(&self) -> &str {
        match self {
            Self::TimedChoice { .. } => "timed_choice",
            Self::Priority(_) => "priority",
            Self::Retry { .. } => "retry",
            Self::Idempotent => "idempotent",
            Self::Trace { .. } => "trace",
            Self::RuntimeTimeout(_) => "runtime_timeout",
            Self::Heartbeat { .. } => "heartbeat",
            Self::Parallel => "parallel",
            Self::Ordered => "ordered",
            Self::MinResponses(_) => "min_responses",
            Self::Custom { key, .. } => key,
        }
    }

    /// Convert from legacy HashMap format.
    ///
    /// Parses known annotation types and falls back to Custom for unknown ones.
    #[must_use]
    pub fn from_legacy(key: &str, value: &str) -> Self {
        match key {
            "timed_choice" if value == "true" => {
                // Duration comes from separate timeout_ms annotation; use zero default
                Self::TimedChoice {
                    duration: Duration::from_secs(0),
                }
            }
            "timeout_ms" => Self::parse_u64_legacy(value)
                .map(|ms| Self::TimedChoice {
                    duration: Duration::from_millis(ms),
                })
                .unwrap_or_else(|| Self::custom_legacy(key, value)),
            "priority" => Self::parse_u32_legacy(value)
                .map(Self::Priority)
                .unwrap_or_else(|| Self::custom_legacy(key, value)),
            "retry" => Self::parse_u32_legacy(value)
                .map(|max_attempts| Self::Retry {
                    max_attempts,
                    delay: None,
                })
                .unwrap_or_else(|| Self::custom_legacy(key, value)),
            "idempotent" if value == "true" => Self::Idempotent,
            "trace" => Self::Trace {
                label: if value.is_empty() || value == "true" {
                    None
                } else {
                    Some(value.to_string())
                },
            },
            "runtime_timeout" => Self::parse_u64_legacy(value)
                .map(|ms| Self::RuntimeTimeout(Duration::from_millis(ms)))
                .unwrap_or_else(|| Self::custom_legacy(key, value)),
            "parallel" if value.is_empty() || value == "true" => Self::Parallel,
            "ordered" if value.is_empty() || value == "true" => Self::Ordered,
            "min_responses" => Self::parse_u32_legacy(value)
                .map(Self::MinResponses)
                .unwrap_or_else(|| Self::custom_legacy(key, value)),
            _ => Self::custom_legacy(key, value),
        }
    }
}
