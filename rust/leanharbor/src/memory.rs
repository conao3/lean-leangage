//! An engine that keeps every tenant's snapshot in this process.

use std::collections::HashMap;
use std::sync::Mutex;

use crate::{Engine, EngineError, Executed, Kernel};

/// Tenant, scope and idempotency key.
type Slot = (u64, String, String);

struct Stored<R> {
    fingerprint: Vec<u8>,
    reply: R,
}

struct State<K: Kernel> {
    tenants: HashMap<u64, K::Snapshot>,
    replies: HashMap<Slot, Stored<K::Reply>>,
}

pub struct MemoryEngine<K: Kernel> {
    state: Mutex<State<K>>,
}

impl<K: Kernel> Default for MemoryEngine<K> {
    fn default() -> Self {
        Self {
            state: Mutex::new(State {
                tenants: HashMap::new(),
                replies: HashMap::new(),
            }),
        }
    }
}

impl<K: Kernel> MemoryEngine<K> {
    pub fn new() -> Self {
        Self::default()
    }

    fn run(
        state: &mut State<K>,
        actor: &K::Principal,
        cmd: &K::Command,
    ) -> Result<K::Reply, K::Error> {
        let tenant = K::tenant(actor);
        let snap = state.tenants.remove(&tenant).unwrap_or_else(K::init);
        match K::transition(actor, &snap, cmd) {
            Ok((ws, reply)) => {
                state.tenants.insert(tenant, K::apply(snap, ws));
                Ok(reply)
            }
            Err(e) => {
                state.tenants.insert(tenant, snap);
                Err(e)
            }
        }
    }
}

impl<K: Kernel> Engine<K> for MemoryEngine<K> {
    fn execute(&self, actor: &K::Principal, cmd: &K::Command) -> Executed<K> {
        let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        Ok(Self::run(&mut state, actor, cmd))
    }

    fn execute_idempotent(
        &self,
        actor: &K::Principal,
        scope: &str,
        key: &str,
        fingerprint: &[u8],
        cmd: &K::Command,
    ) -> Executed<K> {
        let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        let slot = (K::tenant(actor), scope.to_owned(), key.to_owned());
        if let Some(stored) = state.replies.get(&slot) {
            return if stored.fingerprint == fingerprint {
                Ok(Ok(stored.reply.clone()))
            } else {
                Err(EngineError::IdempotencyConflict)
            };
        }
        let result = Self::run(&mut state, actor, cmd);
        if let Ok(reply) = &result {
            let stored = Stored {
                fingerprint: fingerprint.to_vec(),
                reply: reply.clone(),
            };
            state.replies.insert(slot, stored);
        }
        Ok(result)
    }
}
