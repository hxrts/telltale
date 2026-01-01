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

use std::collections::HashMap;
use std::time::Duration;

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
                // Duration is stored separately as timeout_ms
                // Return a placeholder - caller should combine with timeout_ms
                Self::TimedChoice {
                    duration: Duration::from_secs(0),
                }
            }
            "timeout_ms" => {
                if let Ok(ms) = value.parse::<u64>() {
                    Self::TimedChoice {
                        duration: Duration::from_millis(ms),
                    }
                } else {
                    Self::Custom {
                        key: key.to_string(),
                        value: value.to_string(),
                    }
                }
            }
            "priority" => {
                if let Ok(p) = value.parse::<u32>() {
                    Self::Priority(p)
                } else {
                    Self::Custom {
                        key: key.to_string(),
                        value: value.to_string(),
                    }
                }
            }
            "retry" => {
                if let Ok(n) = value.parse::<u32>() {
                    Self::Retry {
                        max_attempts: n,
                        delay: None,
                    }
                } else {
                    Self::Custom {
                        key: key.to_string(),
                        value: value.to_string(),
                    }
                }
            }
            "idempotent" if value == "true" => Self::Idempotent,
            "trace" => Self::Trace {
                label: if value.is_empty() || value == "true" {
                    None
                } else {
                    Some(value.to_string())
                },
            },
            "runtime_timeout" => {
                if let Ok(ms) = value.parse::<u64>() {
                    Self::RuntimeTimeout(Duration::from_millis(ms))
                } else {
                    Self::Custom {
                        key: key.to_string(),
                        value: value.to_string(),
                    }
                }
            }
            _ => Self::Custom {
                key: key.to_string(),
                value: value.to_string(),
            },
        }
    }
}

/// A collection of protocol annotations with typed accessors.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Annotations {
    items: Vec<ProtocolAnnotation>,
}

impl Annotations {
    /// Create an empty annotation set.
    #[must_use]
    pub fn new() -> Self {
        Self { items: Vec::new() }
    }

    /// Create from a single annotation.
    #[must_use]
    pub fn single(annotation: ProtocolAnnotation) -> Self {
        Self {
            items: vec![annotation],
        }
    }

    /// Create from a vector of annotations.
    #[must_use]
    pub fn from_vec(items: Vec<ProtocolAnnotation>) -> Self {
        Self { items }
    }

    /// Convert from legacy HashMap format.
    ///
    /// Special handling for timed_choice which uses two keys (timed_choice + timeout_ms).
    #[must_use]
    pub fn from_legacy_map(map: &HashMap<String, String>) -> Self {
        let mut items = Vec::new();

        // Handle timed_choice specially - it uses two keys
        if map.get("timed_choice").is_some_and(|v| v == "true") {
            let duration = map
                .get("timeout_ms")
                .and_then(|v| v.parse::<u64>().ok())
                .map(Duration::from_millis)
                .unwrap_or_else(|| Duration::from_secs(5));
            items.push(ProtocolAnnotation::TimedChoice { duration });
        }

        // Process other annotations
        for (key, value) in map {
            // Skip timed_choice keys - already handled above
            if key == "timed_choice" || key == "timeout_ms" {
                continue;
            }
            items.push(ProtocolAnnotation::from_legacy(key, value));
        }

        Self { items }
    }

    /// Convert to legacy HashMap format (for backward compatibility).
    #[must_use]
    pub fn to_legacy_map(&self) -> HashMap<String, String> {
        let mut map = HashMap::new();

        for annotation in &self.items {
            match annotation {
                ProtocolAnnotation::TimedChoice { duration } => {
                    map.insert("timed_choice".to_string(), "true".to_string());
                    map.insert("timeout_ms".to_string(), duration.as_millis().to_string());
                }
                ProtocolAnnotation::Priority(p) => {
                    map.insert("priority".to_string(), p.to_string());
                }
                ProtocolAnnotation::Retry { max_attempts, .. } => {
                    map.insert("retry".to_string(), max_attempts.to_string());
                }
                ProtocolAnnotation::Idempotent => {
                    map.insert("idempotent".to_string(), "true".to_string());
                }
                ProtocolAnnotation::Trace { label } => {
                    map.insert(
                        "trace".to_string(),
                        label.clone().unwrap_or_else(|| "true".to_string()),
                    );
                }
                ProtocolAnnotation::RuntimeTimeout(d) => {
                    map.insert("runtime_timeout".to_string(), d.as_millis().to_string());
                }
                ProtocolAnnotation::Heartbeat {
                    interval,
                    on_missing_count,
                } => {
                    map.insert("heartbeat".to_string(), "true".to_string());
                    map.insert(
                        "heartbeat_interval_ms".to_string(),
                        interval.as_millis().to_string(),
                    );
                    map.insert(
                        "heartbeat_on_missing_count".to_string(),
                        on_missing_count.to_string(),
                    );
                }
                ProtocolAnnotation::Custom { key, value } => {
                    map.insert(key.clone(), value.clone());
                }
            }
        }

        map
    }

    /// Add an annotation.
    pub fn push(&mut self, annotation: ProtocolAnnotation) {
        self.items.push(annotation);
    }

    /// Check if empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Get the number of annotations.
    #[must_use]
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Iterate over annotations.
    pub fn iter(&self) -> impl Iterator<Item = &ProtocolAnnotation> {
        self.items.iter()
    }

    /// Iterate mutably over annotations.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut ProtocolAnnotation> {
        self.items.iter_mut()
    }

    /// Check if any annotation satisfies a predicate.
    #[must_use]
    pub fn any<F>(&self, f: F) -> bool
    where
        F: FnMut(&ProtocolAnnotation) -> bool,
    {
        self.items.iter().any(f)
    }

    /// Find the first annotation satisfying a predicate.
    #[must_use]
    pub fn find<F>(&self, f: F) -> Option<&ProtocolAnnotation>
    where
        F: FnMut(&&ProtocolAnnotation) -> bool,
    {
        self.items.iter().find(f)
    }

    /// Get timed choice annotation if present.
    #[must_use]
    pub fn timed_choice(&self) -> Option<Duration> {
        self.items.iter().find_map(|a| a.timed_choice_duration())
    }

    /// Check if this has a timed choice annotation.
    #[must_use]
    pub fn has_timed_choice(&self) -> bool {
        self.items.iter().any(|a| a.is_timed_choice())
    }

    /// Get priority annotation if present.
    #[must_use]
    pub fn priority(&self) -> Option<u32> {
        self.items.iter().find_map(|a| a.priority_value())
    }

    /// Check if marked as idempotent.
    #[must_use]
    pub fn is_idempotent(&self) -> bool {
        self.items.iter().any(|a| a.is_idempotent())
    }

    /// Check if has any trace annotation.
    #[must_use]
    pub fn has_trace(&self) -> bool {
        self.items.iter().any(|a| a.is_trace())
    }

    /// Check if has a heartbeat annotation.
    #[must_use]
    pub fn has_heartbeat(&self) -> bool {
        self.items.iter().any(|a| a.is_heartbeat())
    }

    /// Get heartbeat parameters if present (interval, on_missing_count).
    #[must_use]
    pub fn heartbeat(&self) -> Option<(Duration, u32)> {
        self.items.iter().find_map(|a| a.heartbeat_params())
    }

    /// Check if has a runtime timeout annotation.
    #[must_use]
    pub fn has_runtime_timeout(&self) -> bool {
        self.items.iter().any(|a| a.is_runtime_timeout())
    }

    /// Get runtime timeout duration if present.
    #[must_use]
    pub fn runtime_timeout(&self) -> Option<Duration> {
        self.items.iter().find_map(|a| a.runtime_timeout_duration())
    }

    /// Get a custom annotation value by key.
    #[must_use]
    pub fn custom(&self, key: &str) -> Option<&str> {
        self.items.iter().find_map(|a| a.custom_value(key))
    }

    /// Check if has a specific annotation key (backward compatibility).
    #[must_use]
    pub fn has(&self, key: &str) -> bool {
        self.items.iter().any(|a| a.key() == key)
    }

    /// Get annotation value by key as string (backward compatibility).
    ///
    /// This is primarily for backward compatibility with code that used HashMap.
    #[must_use]
    pub fn get(&self, key: &str) -> Option<String> {
        for annotation in &self.items {
            match annotation {
                ProtocolAnnotation::TimedChoice { duration } if key == "timeout_ms" => {
                    return Some(duration.as_millis().to_string());
                }
                ProtocolAnnotation::TimedChoice { .. } if key == "timed_choice" => {
                    return Some("true".to_string());
                }
                ProtocolAnnotation::Priority(p) if key == "priority" => {
                    return Some(p.to_string());
                }
                ProtocolAnnotation::Custom { key: k, value } if k == key => {
                    return Some(value.clone());
                }
                _ => continue,
            }
        }
        None
    }

    /// Merge annotations from another set.
    pub fn merge(&mut self, other: &Annotations) {
        self.items.extend(other.items.iter().cloned());
    }

    /// Clear all annotations.
    pub fn clear(&mut self) {
        self.items.clear();
    }
}

impl IntoIterator for Annotations {
    type Item = ProtocolAnnotation;
    type IntoIter = std::vec::IntoIter<ProtocolAnnotation>;

    fn into_iter(self) -> Self::IntoIter {
        self.items.into_iter()
    }
}

impl<'a> IntoIterator for &'a Annotations {
    type Item = &'a ProtocolAnnotation;
    type IntoIter = std::slice::Iter<'a, ProtocolAnnotation>;

    fn into_iter(self) -> Self::IntoIter {
        self.items.iter()
    }
}

impl FromIterator<ProtocolAnnotation> for Annotations {
    fn from_iter<I: IntoIterator<Item = ProtocolAnnotation>>(iter: I) -> Self {
        Self {
            items: iter.into_iter().collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_timed_choice_annotation() {
        let ann = ProtocolAnnotation::timed_choice_ms(5000);
        assert!(ann.is_timed_choice());
        assert_eq!(ann.timed_choice_duration(), Some(Duration::from_secs(5)));
        assert_eq!(ann.key(), "timed_choice");
    }

    #[test]
    fn test_priority_annotation() {
        let ann = ProtocolAnnotation::priority(10);
        assert!(ann.is_priority());
        assert_eq!(ann.priority_value(), Some(10));
    }

    #[test]
    fn test_custom_annotation() {
        let ann = ProtocolAnnotation::custom("my_key", "my_value");
        assert!(ann.is_custom_key("my_key"));
        assert_eq!(ann.custom_value("my_key"), Some("my_value"));
        assert_eq!(ann.custom_value("other"), None);
    }

    #[test]
    fn test_from_legacy() {
        let ann = ProtocolAnnotation::from_legacy("priority", "5");
        assert_eq!(ann, ProtocolAnnotation::Priority(5));

        let ann = ProtocolAnnotation::from_legacy("unknown", "value");
        assert!(matches!(ann, ProtocolAnnotation::Custom { .. }));
    }

    #[test]
    fn test_annotations_collection() {
        let mut anns = Annotations::new();
        anns.push(ProtocolAnnotation::timed_choice_ms(1000));
        anns.push(ProtocolAnnotation::priority(5));

        assert!(anns.has_timed_choice());
        assert_eq!(anns.timed_choice(), Some(Duration::from_secs(1)));
        assert_eq!(anns.priority(), Some(5));
        assert_eq!(anns.len(), 2);
    }

    #[test]
    fn test_legacy_map_roundtrip() {
        let mut original = HashMap::new();
        original.insert("timed_choice".to_string(), "true".to_string());
        original.insert("timeout_ms".to_string(), "5000".to_string());
        original.insert("priority".to_string(), "10".to_string());

        let anns = Annotations::from_legacy_map(&original);
        assert!(anns.has_timed_choice());
        assert_eq!(anns.timed_choice(), Some(Duration::from_secs(5)));
        assert_eq!(anns.priority(), Some(10));

        let restored = anns.to_legacy_map();
        assert_eq!(restored.get("timed_choice"), Some(&"true".to_string()));
        assert_eq!(restored.get("timeout_ms"), Some(&"5000".to_string()));
    }

    #[test]
    fn test_backward_compat_get() {
        let mut anns = Annotations::new();
        anns.push(ProtocolAnnotation::timed_choice_ms(5000));

        // These work like the old HashMap::get
        assert_eq!(anns.get("timed_choice"), Some("true".to_string()));
        assert_eq!(anns.get("timeout_ms"), Some("5000".to_string()));
    }
}
