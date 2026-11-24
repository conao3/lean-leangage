//! An engine that keeps every tenant's snapshot in this process.

use std::collections::HashMap;
use std::sync::mpsc;
use std::thread;

use tokio::sync::oneshot;

use crate::{Engine, EngineError, Executed, Idempotency, Kernel};

/// Tenant, scope and idempotency key.
type Slot = (u64, String, String);

struct Stored<R> {
    fingerprint: Vec<u8>,
    reply: R,
}

/// Every tenant's snapshot and the stored replies, used from one thread.
pub struct Core<K: Kernel> {
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
    pub fn new() -> Self {
        Self::default()
    }

    fn run(&mut self, actor: &K::Principal, cmd: &K::Command) -> Result<K::Reply, K::Error> {
        let tenant = K::tenant(actor);
        let snap = self.tenants.remove(&tenant).unwrap_or_else(K::init);
        match K::transition(actor, &snap, cmd) {
            Ok((ws, reply)) => {
                self.tenants.insert(tenant, K::apply(snap, ws));
                Ok(reply)
            }
            Err(e) => {
                self.tenants.insert(tenant, snap);
                Err(e)
            }
        }
    }

    pub fn execute(
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

struct Job<K: Kernel> {
    actor: K::Principal,
    cmd: K::Command,
    idempotency: Option<Idempotency>,
    done: oneshot::Sender<Executed<K>>,
}

/// A [`Core`] on a thread of its own; commands reach it one at a time over a channel.
pub struct MemoryEngine<K: Kernel> {
    jobs: mpsc::Sender<Job<K>>,
}

impl<K: Kernel> Default for MemoryEngine<K> {
    fn default() -> Self {
        let (jobs, queue) = mpsc::channel::<Job<K>>();
        thread::spawn(move || {
            let mut core = Core::<K>::new();
            for job in queue {
                let _ = job
                    .done
                    .send(core.execute(&job.actor, &job.cmd, job.idempotency));
            }
        });
        Self { jobs }
    }
}

impl<K: Kernel> MemoryEngine<K> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<K: Kernel> Engine<K> for MemoryEngine<K> {
    async fn execute(
        &self,
        actor: K::Principal,
        cmd: K::Command,
        idempotency: Option<Idempotency>,
    ) -> Executed<K> {
        let (done, result) = oneshot::channel();
        let job = Job {
            actor,
            cmd,
            idempotency,
            done,
        };
        if self.jobs.send(job).is_err() {
            return Err(EngineError::Stopped);
        }
        result.await.unwrap_or(Err(EngineError::Stopped))
    }
}
