//! The trusted shell around a kernel proved in Lean: an engine that runs one command at a time
//! per tenant, bearer tokens, and the `/rpc` route.

pub mod http;
pub mod memory;
pub mod token;

/// The contract of `Leanharbor.Kernel`, implemented by delegating to functions generated from
/// Lean.
pub trait Kernel: Send + Sync + 'static {
    type Principal: Send + Sync;
    /// One tenant's state.
    type Snapshot: Send + Sync;
    type Command: Send + Sync;
    type WriteSet: Send + Sync;
    type Reply: Send + Sync + Clone;
    /// A refusal; nothing is stored.
    type Error: Send + Sync;

    /// A tenant's snapshot before its first command.
    fn init() -> Self::Snapshot;
    /// The only tenant the principal may read or write.
    fn tenant(actor: &Self::Principal) -> u64;
    fn transition(
        actor: &Self::Principal,
        snap: &Self::Snapshot,
        cmd: &Self::Command,
    ) -> Result<(Self::WriteSet, Self::Reply), Self::Error>;
    fn apply(snap: Self::Snapshot, ws: Self::WriteSet) -> Self::Snapshot;
}

/// Why a request did not reach the kernel's decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EngineError {
    /// The idempotency key was used before with another command.
    IdempotencyConflict,
}

/// The outer result is the engine's, the inner one the kernel's decision.
pub type Executed<K> = Result<Result<<K as Kernel>::Reply, <K as Kernel>::Error>, EngineError>;

pub trait Engine<K: Kernel>: Send + Sync + 'static {
    fn execute(&self, actor: &K::Principal, cmd: &K::Command) -> Executed<K>;

    /// Runs the command once per `(tenant, scope, key)`: a repeat with the same fingerprint
    /// returns the stored reply. Refusals are not stored.
    fn execute_idempotent(
        &self,
        actor: &K::Principal,
        scope: &str,
        key: &str,
        fingerprint: &[u8],
        cmd: &K::Command,
    ) -> Executed<K>;
}
