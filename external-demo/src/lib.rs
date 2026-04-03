#![allow(clippy::type_complexity)]

//! External demo crate for downstream Telltale integrations.
//!
//! This crate is intentionally thin. It demonstrates the recommended
//! integration path for third-party crates:
//! - re-export the `tell!` macro under a domain-friendly name
//! - use `compile_choreography(...)` for validated AST + projection work
//! - consume ordered annotation records from the authoritative AST
//! - rely on the central default content-hash policy
//!
//! # Usage
//!
//! ```ignore
//! use external_demo::{choreography, compile_choreography};
//!
//! choreography! {
//!     protocol Example =
//!       roles Alice, Bob
//!       Alice -> Bob : Request
//!       Bob -> Alice : Response
//! }
//!
//! let compiled = compile_choreography(
//!     "protocol Example =\n  roles Alice, Bob\n  Alice -> Bob : Request\n  Bob -> Alice : Response\n",
//! )?;
//! ```

pub use external_demo_macros::aura_effect_handlers;
pub use telltale::tell as choreography;
pub use telltale::types::{
    Blake3Hasher, ContentIdBlake3, Contentable, DefaultContentHasher, DefaultContentId,
};
pub use telltale::{
    collect_choreography_annotation_records, collect_protocol_annotation_records,
    compile_choreography, compile_choreography_ast, parse_choreography_str, project,
    AnnotationScope, Choreography, ChoreographyRole, CompileArtifactsError, CompiledChoreography,
    DslMessageType, DslProtocol, LocalType, ProjectionError, ProtocolAnnotationRecord,
};

/// Prelude module for downstream demo code.
pub mod prelude {
    pub use telltale::types::{
        Blake3Hasher, ContentIdBlake3, Contentable, DefaultContentHasher, DefaultContentId,
        GlobalType, Label, LocalTypeR, PayloadSort,
    };
    pub use telltale::{
        channel::Bidirectional, session, try_session, Branch, End, Message, Receive, Role, Roles,
        Select, Send,
    };
    pub use telltale::{
        collect_choreography_annotation_records, collect_protocol_annotation_records,
        compile_choreography, compile_choreography_ast, parse_choreography_str, project,
        AnnotationScope, Choreography, ChoreographyRole, CompileArtifactsError,
        CompiledChoreography, DslMessageType, DslProtocol, LocalType, ProjectionError,
        ProtocolAnnotationRecord,
    };

    pub use external_demo_macros::aura_effect_handlers;
    pub use futures::{channel::mpsc, executor, try_join};
    pub use telltale::tell as choreography;
}

/// Session-typed runtime surface from `telltale`.
pub mod session {
    pub use telltale::{
        channel, session, try_session, Branch, End, Message, Receive, Role, Roles, Select, Send,
    };
}

/// Recommended integration API surface for downstream crates.
pub mod integration {
    pub use telltale::{
        collect_choreography_annotation_records, collect_protocol_annotation_records,
        compile_choreography, compile_choreography_ast, parse_choreography_str, project,
        AnnotationScope, Choreography, ChoreographyRole, CompileArtifactsError,
        CompiledChoreography, DslMessageType, DslProtocol, LocalType, ProjectionError,
        ProtocolAnnotationRecord,
    };
}

/// Content-addressing policy surface for downstream crates.
pub mod hashing {
    pub use telltale::types::{
        Blake3Hasher, ContentId, ContentIdBlake3, Contentable, DefaultContentHasher,
        DefaultContentId, Hasher,
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prelude_exposes_modern_integration_surface() {
        let _compile = compile_choreography;
        let _hash: Option<DefaultContentId> = None;
    }

    #[test]
    fn prelude_imports_compile() {
        use crate::prelude::*;

        let _compile = compile_choreography;
        let _content_id: Option<DefaultContentId> = None;
    }
}
