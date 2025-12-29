//! Client role implementation.
//!
//! The client role represents the HTTP client making requests through the proxy.

use crate::{cache::Cache, origin::Origin, proxy::Proxy, Channel, Request, Response, Result};
use hyper::Body;
use rumpsteak_aura::{channel::Nil, session, try_session, End, Receive, Role, Send};
use std::{any::Any, marker};
use tracing::error;

/// The client role that sends requests and receives responses.
#[derive(Role)]
#[message(Box<dyn Any + marker::Send>)]
pub struct Client {
    #[route(Proxy)]
    pub(crate) proxy: Channel,
    #[route(Cache)]
    pub(crate) cache: Nil,
    #[route(Origin)]
    pub(crate) origin: Nil,
}

#[session]
type Session = Send<Proxy, Request, Receive<Proxy, Response, End>>;

async fn try_run(
    role: &mut Client,
    request: hyper::Request<Body>,
) -> Result<hyper::Response<Body>> {
    try_session(role, |s: Session<'_, Client>| async {
        let s = s.send(request).await?;
        let (response, s) = s.receive().await?;
        Ok((response.into_response(), s))
    })
    .await
}

/// Runs the client role protocol.
///
/// Sends an HTTP request to the proxy and receives the response.
pub async fn run(
    role: &mut Client,
    request: hyper::Request<Body>,
) -> Result<hyper::Response<Body>> {
    let result = try_run(role, request).await;
    if let Err(err) = &result {
        error!("{}", err);
    }

    result
}
