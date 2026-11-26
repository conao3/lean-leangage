//! An engine that keeps every tenant's snapshot in this process.

use std::collections::HashMap;
use std::sync::Mutex;

use crate::{Engine, EngineError, Executed, Idempotency, Kernel};

/// Tenant, scope and idempotency key.
type Slot = (u64, String, String);

struct Stored<R> {
    fingerprint: Vec<u8>,
    reply: R,
}

/// Every tenant's snapshot and the stored replies.
struct Core<K: Kernel> {
    tenants: HashMap<u64, K::Snapshot>,
    replies: HashMap<Slot, Stored<K::Reply>>,
}

impl<K: Kernel> Default for Core<K> {
    fn default() -> Self {
        Self {
            tenants: HashMap::new(),
            replies: HashMap::new(),
        }
    }
}

impl<K: Kernel> Core<K> {
    fn run(&mut self, actor: &K::Principal, cmd: &K::Command) -> Result<K::Reply, K::Error> {
        let snap = self.tenants.entry(K::tenant(actor)).or_insert_with(K::init);
        K::lend(snap, |view| match K::transition(actor, &view, cmd) {
            Ok((ws, reply)) => (K::apply(view, ws), Ok(reply)),
            Err(e) => (view, Err(e)),
        })
    }

    fn execute(
        &mut self,
        actor: &K::Principal,
        cmd: &K::Command,
        idempotency: Option<Idempotency>,
    ) -> Executed<K> {
        let Some(idempotency) = idempotency else {
            return Ok(self.run(actor, cmd));
        };
        let slot = (K::tenant(actor), idempotency.scope, idempotency.key);
        if let Some(stored) = self.replies.get(&slot) {
            return if stored.fingerprint == idempotency.fingerprint {
                Ok(Ok(stored.reply.clone()))
            } else {
                Err(EngineError::IdempotencyConflict)
            };
        }
        let result = self.run(actor, cmd);
        if let Ok(reply) = &result {
            let stored = Stored {
                fingerprint: idempotency.fingerprint,
                reply: reply.clone(),
            };
            self.replies.insert(slot, stored);
        }
        Ok(result)
    }
}

/// One lock around every tenant's snapshot: commands run one at a time, on the caller's thread.
pub struct MemoryEngine<K: Kernel> {
    core: Mutex<Core<K>>,
}

impl<K: Kernel> Default for MemoryEngine<K> {
    fn default() -> Self {
        Self {
            core: Mutex::new(Core::default()),
        }
    }
}

impl<K: Kernel> MemoryEngine<K> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Shows `f` the tenant's snapshot; `None` before the tenant's first command.
    pub fn inspect<R>(&self, tenant: u64, f: impl FnOnce(&K::View) -> R) -> Option<R> {
        let mut core = self.core.lock().ok()?;
        let snap = core.tenants.get_mut(&tenant)?;
        Some(K::lend(snap, |view| {
            let seen = f(&view);
            (view, seen)
        }))
    }
}

impl<K: Kernel> Engine<K> for MemoryEngine<K> {
    async fn execute(
        &self,
        actor: K::Principal,
        cmd: K::Command,
        idempotency: Option<Idempotency>,
    ) -> Executed<K> {
        match self.core.lock() {
            Ok(mut core) => core.execute(&actor, &cmd, idempotency),
            Err(_) => Err(EngineError::Stopped),
        }
    }
}
