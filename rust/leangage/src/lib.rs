//! The trusted server around a kernel proved in Lean: an engine that runs one command at a time
//! per tenant, bearer tokens, and the `/rpc` route. `leangage-pg` holds the engine that stores
//! the snapshots in PostgreSQL. `sql` is the SQL compiler generated from
//! `lean/Leangage/Sql.lean`, `token_format` the functions that write and split tokens,
//! generated from `lean/Leangage/Token.lean`, `json_format` the JSON writer, generated from
//! `lean/Leangage/Json.lean`, `json_lexemes` the tokens of a JSON text and the functions that
//! read a number token and the members of an object, generated from
//! `lean/Leangage/Json/Lexemes.lean`, `json_text` the conversion of a body into those tokens
//! with serde_json, and `http_format` the functions that decide the answers a server gives by
//! itself, generated from `lean/Leangage/Http.lean`.

#[rustfmt::skip]
#[path = "gen/mod.rs"]
pub mod generated;
pub mod http;
pub mod json_text;
pub mod memory;
pub mod token;

pub use generated::leangage_http as http_format;
pub use generated::leangage_json as json_format;
pub use generated::leangage_json_lexemes as json_lexemes;
pub use generated::leangage_sql as sql;
pub use generated::leangage_token as token_format;

/// The contract of `Leangage.Kernel`, implemented by delegating to functions generated from
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
    /// Whether the command only reads: `ReadOnlySound` says it then writes nothing.
    fn read_only(cmd: &Self::Command) -> bool;
}

/// The contract of `Leangage.Storage`: how a kernel's snapshots are stored in PostgreSQL,
/// implemented by delegating to functions generated from Lean, and the bytes an engine stores
/// for a reply under an idempotency key.
pub trait Storage: Kernel {
    /// The tables, in the order `load` receives their rows.
    fn tables() -> Vec<sql::Tab>;
    /// The snapshot of the rows of each table; `None` when a row is not one the kernel stores.
    fn load(rows: Vec<Vec<Vec<sql::Val>>>) -> Option<Self::Snapshot>;
    /// The rows a write set stores.
    fn writes(ws: &Self::WriteSet) -> Vec<sql::Write>;
    /// The stored form of a reply. Trusted: no theorem covers it.
    fn encode_reply(reply: &Self::Reply) -> Vec<u8>;
    /// The reply `encode_reply` stored; `None` for bytes it does not write.
    fn decode_reply(bytes: &[u8]) -> Option<Self::Reply>;
}

/// Why a request did not reach the kernel's decision, or its decision was not stored.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EngineError {
    /// The idempotency key was used before with another command.
    IdempotencyConflict,
    /// The engine no longer runs commands: a command panicked while it held the snapshots.
    Stopped,
    /// Every attempt failed to serialize or lost its connection; none committed, except that a
    /// request with an idempotency key may have committed on an attempt whose COMMIT was lost.
    RetriesExhausted,
    /// The connection was lost during the COMMIT of a request without an idempotency key: it may
    /// or may not have committed.
    CommitUnknown,
    /// The database failed the request, which did not commit.
    Database(String),
    /// The stored rows or reply do not decode, a write set does not compile, or a read-only
    /// command wrote. Nothing was committed.
    Broken(String),
}

impl std::fmt::Display for EngineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EngineError::IdempotencyConflict => write!(f, "idempotency key reused"),
            EngineError::Stopped => write!(f, "engine stopped"),
            EngineError::RetriesExhausted => write!(f, "retries exhausted"),
            EngineError::CommitUnknown => write!(f, "commit outcome unknown"),
            EngineError::Database(e) => write!(f, "database: {e}"),
            EngineError::Broken(e) => write!(f, "engine: {e}"),
        }
    }
}

impl std::error::Error for EngineError {}

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
