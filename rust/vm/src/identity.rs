//! Identity model aligned with Lean VM domain interfaces.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

/// Participant identifier.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ParticipantId(pub String);

impl From<&str> for ParticipantId {
    fn from(value: &str) -> Self {
        Self(value.to_string())
    }
}

/// Site identifier.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SiteId(pub String);

impl From<&str> for SiteId {
    fn from(value: &str) -> Self {
        Self(value.to_string())
    }
}

/// Lean-style identity model for topology and capabilities.
pub trait IdentityModel {
    /// Participant type.
    type ParticipantId: Clone + Ord;
    /// Site type.
    type SiteId: Clone + Ord;

    /// Enumerate known sites.
    fn sites(&self) -> Vec<Self::SiteId>;
    /// Resolve a stable site display name.
    fn site_name(&self, site: &Self::SiteId) -> String;
    /// Capabilities provided by one site.
    fn site_capabilities(&self, site: &Self::SiteId) -> BTreeSet<String>;
    /// Set of reliable directed links.
    fn reliable_edges(&self) -> BTreeSet<(Self::SiteId, Self::SiteId)>;

    /// Lean-name compatibility wrapper.
    #[allow(non_snake_case)]
    fn siteName(&self, site: &Self::SiteId) -> String {
        self.site_name(site)
    }

    /// Lean-name compatibility wrapper.
    #[allow(non_snake_case)]
    fn siteCapabilities(&self, site: &Self::SiteId) -> BTreeSet<String> {
        self.site_capabilities(site)
    }

    /// Lean-name compatibility wrapper.
    #[allow(non_snake_case)]
    fn reliableEdges(&self) -> BTreeSet<(Self::SiteId, Self::SiteId)> {
        self.reliable_edges()
    }
}

/// Simple static identity topology model.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct StaticIdentityModel {
    /// Site metadata keyed by identifier.
    pub sites: BTreeMap<SiteId, SiteInfo>,
    /// Reliable directed links.
    pub reliable_edges: BTreeSet<(SiteId, SiteId)>,
}

/// Site metadata.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SiteInfo {
    /// Display name for the site.
    pub name: String,
    /// Site capability labels.
    pub capabilities: BTreeSet<String>,
}

impl IdentityModel for StaticIdentityModel {
    type ParticipantId = ParticipantId;
    type SiteId = SiteId;

    fn sites(&self) -> Vec<Self::SiteId> {
        self.sites.keys().cloned().collect()
    }

    fn site_name(&self, site: &Self::SiteId) -> String {
        self.sites
            .get(site)
            .map(|info| info.name.clone())
            .unwrap_or_else(|| site.0.clone())
    }

    fn site_capabilities(&self, site: &Self::SiteId) -> BTreeSet<String> {
        self.sites
            .get(site)
            .map(|info| info.capabilities.clone())
            .unwrap_or_default()
    }

    fn reliable_edges(&self) -> BTreeSet<(Self::SiteId, Self::SiteId)> {
        self.reliable_edges.clone()
    }
}
