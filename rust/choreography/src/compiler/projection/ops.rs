use super::merge::{merge_labeled_local_types, LabeledLocalType};
use super::*;
use proc_macro2::Ident;

impl<'a> ProjectionContext<'a> {
    pub(super) fn merge_parallel_projections(
        &mut self,
        projections: Vec<LocalType>,
    ) -> Result<LocalType, ProjectionError> {
        // Remove End projections as they don't contribute
        let non_end: Vec<_> = projections
            .into_iter()
            .filter(|p| p != &LocalType::End)
            .collect();

        match non_end.len() {
            0 => Ok(LocalType::End),
            1 => Ok(non_end
                .into_iter()
                .next()
                .expect("non_end must have exactly one element")),
            _ => {
                // Check for conflicts
                self.check_parallel_conflicts(&non_end)?;

                // Multiple non-trivial projections - merge them
                // Interleaving is allowed in parallel composition
                // The merge creates a sequential composition (non-deterministic order)
                let mut merged = LocalType::End;
                for proj in non_end.into_iter().rev() {
                    merged = self.sequential_merge(proj, merged);
                }
                Ok(merged)
            }
        }
    }

    /// Check for conflicts between parallel projections
    ///
    /// Returns an error if the projections have incompatible operations
    /// that cannot be safely interleaved.
    fn check_parallel_conflicts(&self, projections: &[LocalType]) -> Result<(), ProjectionError> {
        // Check for conflicting sends
        let mut send_targets = Vec::new();
        let mut recv_sources = Vec::new();

        for proj in projections {
            match proj {
                LocalType::Send { to, .. } => {
                    if send_targets.contains(to) {
                        return Err(ProjectionError::InconsistentParallel);
                    }
                    send_targets.push(to.clone());
                }
                LocalType::Receive { from, .. } => {
                    if recv_sources.contains(from) {
                        return Err(ProjectionError::InconsistentParallel);
                    }
                    recv_sources.push(from.clone());
                }
                LocalType::Select { to, .. } => {
                    if send_targets.contains(to) {
                        return Err(ProjectionError::InconsistentParallel);
                    }
                    send_targets.push(to.clone());
                }
                LocalType::Branch { from, .. } => {
                    if recv_sources.contains(from) {
                        return Err(ProjectionError::InconsistentParallel);
                    }
                    recv_sources.push(from.clone());
                }
                _ => {
                    // Other types are compatible with parallel composition
                }
            }
        }

        Ok(())
    }

    fn sequential_merge(&self, first: LocalType, second: LocalType) -> LocalType {
        // Merge two local types sequentially
        match (first, second) {
            (LocalType::End, other) | (other, LocalType::End) => other,
            (first, second) => {
                // Chain them together
                self.append_continuation(first, second)
            }
        }
    }

    fn append_continuation(&self, local_type: LocalType, continuation: LocalType) -> LocalType {
        Self::append_continuation_static(local_type, continuation)
    }

    fn append_continuation_static(local_type: LocalType, continuation: LocalType) -> LocalType {
        match local_type {
            LocalType::Send {
                to,
                message,
                continuation: cont,
            } => LocalType::Send {
                to,
                message,
                continuation: Box::new(Self::append_continuation_static(
                    *cont,
                    continuation.clone(),
                )),
            },
            LocalType::Receive {
                from,
                message,
                continuation: cont,
            } => LocalType::Receive {
                from,
                message,
                continuation: Box::new(Self::append_continuation_static(
                    *cont,
                    continuation.clone(),
                )),
            },
            LocalType::End => continuation,
            // For other types, just return as-is with continuation appended at the end
            other => other,
        }
    }

    pub(super) fn project_rec(
        &mut self,
        label: &proc_macro2::Ident,
        body: &Protocol,
    ) -> Result<LocalType, ProjectionError> {
        let body_projection = self.project_protocol(body)?;

        // Only include Rec if the body actually uses this role
        if body_projection == LocalType::End {
            Ok(LocalType::End)
        } else {
            Ok(LocalType::Rec {
                label: label.clone(),
                body: Box::new(body_projection),
            })
        }
    }

    pub(super) fn project_var(
        &mut self,
        label: &proc_macro2::Ident,
    ) -> Result<LocalType, ProjectionError> {
        Ok(LocalType::Var(label.clone()))
    }

    pub(super) fn merge_choice_continuations(
        &mut self,
        branches: &[Branch],
    ) -> Result<LocalType, ProjectionError> {
        // Project each branch and preserve its label
        let mut labeled_projections = Vec::new();

        for branch in branches {
            let projection = self.project_protocol(&branch.protocol)?;
            labeled_projections.push((branch.label.clone(), projection));
        }

        // Check if all projections are identical (common case)
        let projections_only: Vec<_> = labeled_projections.iter().map(|(_, p)| p).collect();
        if projections_only.windows(2).all(|w| w[0] == w[1]) {
            Ok(labeled_projections
                .into_iter()
                .next()
                .expect("projections must be non-empty when windows returned true")
                .1)
        } else {
            // Different projections per branch - need to merge with label awareness
            self.merge_local_types_labeled(labeled_projections)
        }
    }

    /// Merge multiple labeled local types preserving choice labels.
    ///
    /// This is used for merging choice continuations where we need to preserve
    /// the original choice labels. When a receiver gets different messages per branch,
    /// the resulting Branch node should use the semantic choice labels, not message names.
    fn merge_local_types_labeled(
        &self,
        labeled_projections: Vec<(Ident, LocalType)>,
    ) -> Result<LocalType, ProjectionError> {
        if labeled_projections.is_empty() {
            return Ok(LocalType::End);
        }

        // Filter out End types as they're neutral for merging
        let non_end: Vec<_> = labeled_projections
            .into_iter()
            .filter(|(_, p)| p != &LocalType::End)
            .collect();

        if non_end.is_empty() {
            return Ok(LocalType::End);
        }

        // Fold the merge operation over all projections, preserving labels
        // Safety: non_end is non-empty (checked above)
        let mut iter = non_end.into_iter();
        let (first_label, first_type) = iter.next().expect("non-empty after is_empty check");
        let mut result = LabeledLocalType {
            label: first_label,
            local_type: first_type,
        };

        for (label, next) in iter {
            result = merge_labeled_local_types(
                &result,
                &LabeledLocalType {
                    label,
                    local_type: next,
                },
            )?;
        }

        Ok(result.local_type)
    }
}
