//! Cache role implementation for Redis-backed storage.
//!
//! The cache role manages a distributed cache using Redis, with support for
//! optimistic locking to coordinate concurrent access.

use crate::{client::Client, origin::Origin, proxy::Proxy, wrap, Channel, Entry, Result};
use fred::prelude::{Client as RedisClient, KeysInterface, SetOptions::NX, Value};
use rand::{rngs::StdRng, Rng, SeedableRng};
use rumpsteak_aura::{channel::Nil, session, try_session, Branch, End, Receive, Role, Send};
use std::{any::Any, marker, time::Duration};
use tokio::time;
use tracing::{debug, error};

const MAX_RETRY_DELAY: u64 = 1000;

/// The cache role that manages Redis-backed storage.
#[derive(Role)]
#[message(Box<dyn Any + marker::Send>)]
pub struct Cache {
    #[route(Client)]
    pub(crate) client: Nil,
    #[route(Proxy)]
    pub(crate) proxy: Channel,
    #[route(Origin)]
    pub(crate) origin: Nil,
}

/// Message to acquire a lock on a cache key.
pub struct Lock(pub(crate) String);

/// Message indicating lock has been acquired.
pub struct Locked;

/// Message to release a lock.
pub struct Unlock;

/// Message to load an entry from the cache.
pub struct Load;

/// Message to store an entry in the cache.
pub struct Store(pub(crate) Entry);

/// Message to remove an entry from the cache.
pub struct Remove;

#[session]
type Session = Receive<Proxy, Lock, Send<Proxy, Locked, Branch<Proxy, Choice>>>;

#[session]
enum Choice {
    Load(Load, Send<Proxy, Option<Entry>, Branch<Proxy, Choice>>),
    Store(Store, Branch<Proxy, Choice>),
    Remove(Remove, Branch<Proxy, Choice>),
    Unlock(Unlock, End),
}

/// State of the cache replica.
///
/// Tracks whether the local copy has been modified since being loaded.
enum Replica {
    /// No replica loaded yet
    None,
    /// Replica loaded and unchanged
    Clean(Option<Entry>),
    /// Replica has been modified
    Dirty(Option<Entry>),
}

async fn try_run(role: &mut Cache, redis: &RedisClient) -> Result<()> {
    let mut rng = StdRng::from_entropy();
    try_session(role, |s: Session<'_, Cache>| async {
        let (Lock(mut lock), s) = s.receive().await?;
        let size = lock.len();
        lock.push_str(":lock");
        let key = &lock[..size];

        while !wrap(
            redis
                .set::<Value, _, _>(&lock, 0, None, Some(NX), false)
                .await,
        )?
        .is_ok()
        {
            let delay = rng.gen_range(0..MAX_RETRY_DELAY);
            time::sleep(Duration::from_millis(delay)).await;
        }

        let mut s = s.send(Locked).await?;
        let mut replica = Replica::None;

        loop {
            s = match s.branch().await? {
                Choice::Load(Load, s) => loop {
                    match &replica {
                        Replica::None => {
                            let entry: Value = wrap(redis.get(key).await)?;
                            replica = Replica::Clean(match entry.as_bytes() {
                                Some(bytes) => Some(bincode::deserialize(bytes)?),
                                None => None,
                            });
                        }
                        Replica::Clean(entry) | Replica::Dirty(entry) => {
                            break s.send(entry.clone()).await?
                        }
                    }
                },
                Choice::Store(Store(cacheable), s) => {
                    debug!("storing a new cache entry");
                    replica = Replica::Dirty(Some(cacheable));
                    s
                }
                Choice::Remove(Remove, s) => {
                    debug!("removing a cache entry");
                    replica = Replica::Dirty(None);
                    s
                }
                Choice::Unlock(Unlock, s) => {
                    if let Replica::Dirty(entry) = replica {
                        debug!("flushing changes to cache");
                        match entry {
                            Some(entry) => {
                                let value = Value::Bytes(bincode::serialize(&entry)?.into());
                                let value: Value = wrap(
                                    redis
                                        .set::<Value, _, _>(key, value, None, None, false)
                                        .await,
                                )?;
                                assert!(value.is_ok());
                            }
                            None => {
                                let deleted: Value = wrap(redis.del::<Value, _>(key).await)?;
                                assert_eq!(deleted, Value::Integer(1));
                            }
                        }
                    }

                    let deleted: Value = wrap(redis.del::<Value, _>(&lock).await)?;
                    assert_eq!(deleted, Value::Integer(1));
                    return Ok(((), s));
                }
            }
        }
    })
    .await
}

/// Runs the cache role protocol.
///
/// Manages cache storage with optimistic locking using Redis.
pub async fn run(role: &mut Cache, redis: &RedisClient) -> Result<()> {
    let result = try_run(role, redis).await;
    if let Err(err) = &result {
        error!("{}", err);
    }

    result
}
