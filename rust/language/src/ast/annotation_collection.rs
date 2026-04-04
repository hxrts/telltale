//! Typed accessors for protocol annotation collections.

use super::{DslAnnotationEntry, ProtocolAnnotation};
use std::collections::HashMap;
use std::time::Duration;

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

    /// Create from ordered raw DSL entries.
    ///
    /// Entry order is preserved exactly. Known annotations are lowered to their
    /// typed variants; unknown entries remain `Custom`.
    #[must_use]
    pub fn from_dsl_entries(entries: &[DslAnnotationEntry]) -> Self {
        let mut items = Vec::new();
        let mut timed_choice = false;
        let mut timeout_ms = None;

        for entry in entries {
            if entry.key == "timed_choice" && entry.value == "true" {
                timed_choice = true;
                continue;
            }
            if entry.key == "timeout_ms" {
                timeout_ms = entry.value.parse::<u64>().ok().map(Duration::from_millis);
                continue;
            }
            items.push(ProtocolAnnotation::parse_dsl_entry(
                &entry.key,
                &entry.value,
            ));
        }

        if timed_choice || timeout_ms.is_some() {
            items.insert(
                0,
                ProtocolAnnotation::TimedChoice {
                    duration: timeout_ms.unwrap_or_else(|| Duration::from_secs(5)),
                },
            );
        }

        Self { items }
    }

    pub fn from_dsl_map(map: &HashMap<String, String>) -> Self {
        let mut entries: Vec<_> = map.iter().collect();
        entries.sort_by(|(key_a, _), (key_b, _)| key_a.cmp(key_b));
        let entries = entries
            .into_iter()
            .map(|(key, value)| DslAnnotationEntry::new(key.clone(), value.clone()))
            .collect::<Vec<_>>();
        Self::from_dsl_entries(&entries)
    }

    pub fn dsl_map(&self) -> HashMap<String, String> {
        let mut map = HashMap::new();

        for annotation in &self.items {
            for (key, value) in annotation.dsl_entries() {
                map.insert(key, value);
            }
        }

        map
    }

    /// Return raw DSL entries in stable order.
    #[must_use]
    pub fn dsl_entries(&self) -> Vec<DslAnnotationEntry> {
        self.items
            .iter()
            .flat_map(|annotation| {
                annotation
                    .dsl_entries()
                    .into_iter()
                    .map(|(key, value)| DslAnnotationEntry::new(key, value))
            })
            .collect()
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

    /// Check if has a parallel annotation.
    #[must_use]
    pub fn has_parallel(&self) -> bool {
        self.items.iter().any(|a| a.is_parallel())
    }

    /// Check if has an ordered annotation.
    #[must_use]
    pub fn has_ordered(&self) -> bool {
        self.items.iter().any(|a| a.is_ordered())
    }

    /// Check if has a min_responses annotation.
    #[must_use]
    pub fn has_min_responses(&self) -> bool {
        self.items.iter().any(|a| a.is_min_responses())
    }

    /// Get min_responses value if present.
    #[must_use]
    pub fn min_responses(&self) -> Option<u32> {
        self.items.iter().find_map(|a| a.min_responses_value())
    }

    /// Get a custom annotation value by key.
    #[must_use]
    pub fn custom(&self, key: &str) -> Option<&str> {
        self.items.iter().find_map(|a| a.custom_value(key))
    }

    /// Get every custom annotation value for a key in source order.
    #[must_use]
    pub fn custom_values(&self, key: &str) -> Vec<&str> {
        self.items
            .iter()
            .filter_map(|annotation| annotation.custom_value(key))
            .collect()
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
    fn test_parse_dsl_entry() {
        let ann = ProtocolAnnotation::parse_dsl_entry("priority", "5");
        assert_eq!(ann, ProtocolAnnotation::Priority(5));

        let ann = ProtocolAnnotation::parse_dsl_entry("unknown", "value");
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
    fn test_map_roundtrip() {
        let mut original = HashMap::new();
        original.insert("timed_choice".to_string(), "true".to_string());
        original.insert("timeout_ms".to_string(), "5000".to_string());
        original.insert("priority".to_string(), "10".to_string());

        let anns = Annotations::from_dsl_map(&original);
        assert!(anns.has_timed_choice());
        assert_eq!(anns.timed_choice(), Some(Duration::from_secs(5)));
        assert_eq!(anns.priority(), Some(10));

        let restored = anns.dsl_map();
        assert_eq!(restored.get("timed_choice"), Some(&"true".to_string()));
        assert_eq!(restored.get("timeout_ms"), Some(&"5000".to_string()));
    }

    #[test]
    fn test_dsl_entries_preserve_order() {
        let entries = vec![
            DslAnnotationEntry::new("guard_capability", "chat:send"),
            DslAnnotationEntry::new("flow_cost", "10"),
            DslAnnotationEntry::new("journal_facts", "sent"),
        ];

        let annotations = Annotations::from_dsl_entries(&entries);
        let restored = annotations.dsl_entries();

        assert_eq!(restored, entries);
    }

    #[test]
    fn test_custom_values_preserve_duplicates() {
        let entries = vec![
            DslAnnotationEntry::new("guard_capability", "chat:send"),
            DslAnnotationEntry::new("guard_capability", "chat:audit"),
        ];

        let annotations = Annotations::from_dsl_entries(&entries);
        assert_eq!(
            annotations.custom_values("guard_capability"),
            vec!["chat:send", "chat:audit"]
        );
        assert_eq!(annotations.custom("guard_capability"), Some("chat:send"));
    }

    #[test]
    fn test_parallel_annotation() {
        let ann = ProtocolAnnotation::parallel();
        assert!(ann.is_parallel());
        assert!(!ann.is_ordered());
    }

    #[test]
    fn test_ordered_annotation() {
        let ann = ProtocolAnnotation::ordered();
        assert!(ann.is_ordered());
        assert!(!ann.is_parallel());
    }

    #[test]
    fn test_min_responses_annotation() {
        let ann = ProtocolAnnotation::min_responses(3);
        assert!(ann.is_min_responses());
        assert_eq!(ann.min_responses_value(), Some(3));
    }

    #[test]
    fn test_annotations_parallel_ordered() {
        let mut anns = Annotations::new();
        anns.push(ProtocolAnnotation::parallel());
        anns.push(ProtocolAnnotation::min_responses(5));

        assert!(anns.has_parallel());
        assert!(!anns.has_ordered());
        assert!(anns.has_min_responses());
        assert_eq!(anns.min_responses(), Some(5));
    }

    #[test]
    fn test_parse_dsl_entry_parallel() {
        let ann = ProtocolAnnotation::parse_dsl_entry("parallel", "true");
        assert_eq!(ann, ProtocolAnnotation::Parallel);

        let ann = ProtocolAnnotation::parse_dsl_entry("ordered", "true");
        assert_eq!(ann, ProtocolAnnotation::Ordered);

        let ann = ProtocolAnnotation::parse_dsl_entry("parallel", "");
        assert_eq!(ann, ProtocolAnnotation::Parallel);

        let ann = ProtocolAnnotation::parse_dsl_entry("ordered", "");
        assert_eq!(ann, ProtocolAnnotation::Ordered);

        let ann = ProtocolAnnotation::parse_dsl_entry("min_responses", "3");
        assert_eq!(ann, ProtocolAnnotation::MinResponses(3));
    }

    #[test]
    fn test_to_map_new_annotations() {
        let mut anns = Annotations::new();
        anns.push(ProtocolAnnotation::Parallel);
        anns.push(ProtocolAnnotation::Ordered);
        anns.push(ProtocolAnnotation::MinResponses(5));

        let map = anns.dsl_map();
        assert_eq!(map.get("parallel"), Some(&"true".to_string()));
        assert_eq!(map.get("ordered"), Some(&"true".to_string()));
        assert_eq!(map.get("min_responses"), Some(&"5".to_string()));
    }
}
