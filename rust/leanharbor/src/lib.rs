//! The trusted shell around a kernel proved in Lean: an engine that runs one command at a time
//! per tenant, bearer tokens, and the `/rpc` route.

pub mod http;
pub mod memory;
pub mod token;

/// The contract of `Leanharbor.Kernel`, implemented by delegating to functions generated from
/// Lean.
pub trait Kernel: 'static {
    type Principal: Send + 'static;
    /// One tenant's state as an engine stores it. It has one owner and moves between threads.
    type Snapshot: Send + 'static;
    /// A stored snapshot while one command runs on it. It may be a value of Lean's that stays on
    /// one thread.
    type View;
    type Command: Send + 'static;
    type WriteSet;
    type Reply: Send + Clone + 'static;
    /// A refusal; nothing is stored.
    type Error: Send + 'static;

    /// A tenant's snapshot before its first command.
    fn init() -> Self::Snapshot;
    /// The only tenant the principal may read or write.
    fn tenant(actor: &Self::Principal) -> u64;
    /// Lends the stored snapshot to `f` and stores the view that `f` returns.
    fn lend<R>(snap: &mut Self::Snapshot, f: impl FnOnce(Self::View) -> (Self::View, R)) -> R;
    fn transition(
        actor: &Self::Principal,
        snap: &Self::View,
        cmd: &Self::Command,
    ) -> Result<(Self::WriteSet, Self::Reply), Self::Error>;
    fn apply(snap: Self::View, ws: Self::WriteSet) -> Self::View;
}

/// Why a request did not reach the kernel's decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EngineError {
    /// The idempotency key was used before with another command.
    IdempotencyConflict,
    /// The engine no longer runs commands: a command panicked while it held the snapshots.
    Stopped,
}

/// The outer result is the engine's, the inner one the kernel's decision.
pub type Executed<K> = Result<Result<<K as Kernel>::Reply, <K as Kernel>::Error>, EngineError>;

/// Scope, key and fingerprint of a request that carries an idempotency key.
pub struct Idempotency {
    pub scope: String,
    pub key: String,
    pub fingerprint: Vec<u8>,
}

pub trait Engine<K: Kernel>: Send + Sync + 'static {
    /// Runs the command. With `idempotency`, runs it once per `(tenant, scope, key)`: a repeat
    /// with the same fingerprint returns the stored reply. Refusals are not stored.
    fn execute(
        &self,
        actor: K::Principal,
        cmd: K::Command,
        idempotency: Option<Idempotency>,
    ) -> impl Future<Output = Executed<K>> + Send;
}
