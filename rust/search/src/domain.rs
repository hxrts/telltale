//! Domain-extension boundary for weighted graph search.
//!
//! Downstream crates are expected to supply node, edge, cost, heuristic, and
//! graph-epoch semantics through this boundary.

/// Marker trait for future graph-search domains.
pub trait SearchDomainMarker {}
