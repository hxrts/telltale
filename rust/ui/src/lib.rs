//! Portable Dioxus UI core for the Telltale simulator tooling webapp.
//!
//! This crate owns reusable layout, routing state, and rendering helpers while
//! keeping browser APIs in `telltale-web` and semantic artifact truth in
//! `telltale-viewer`.

#![allow(missing_docs)]
#![allow(clippy::incompatible_msrv)]

pub mod components;
pub mod demo;
pub mod loading;
pub mod overlays;
pub mod pages;
pub mod shell;
pub mod types;

pub use demo::demo_workspace;
pub use loading::load_workspace_from_service;
pub use shell::{TelltaleUiRoot, ViewerFrame};
pub use types::*;
