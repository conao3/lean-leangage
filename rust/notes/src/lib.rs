//! The notes: the kernel is `lean/Notes/Kernel.lean`, its tables `lean/Notes/Store.lean` and its
//! requests and responses `lean/Notes/Wire.lean`, all generated to `src/gen/`. Its
//! `transition` is the kernel's `handle` behind the guard of `lean/Leangage/Authz.lean`. [`Api`]
//! passes each call on to `wire`.

#[rustfmt::skip]
#[path = "gen/mod.rs"]
pub mod generated;
/// The notes' tables, generated from `Notes.Store` with the kernel's types and the types of
/// `leangage::sql`.
#[rustfmt::skip]
#[allow(dead_code, non_snake_case, non_camel_case_types, unused_imports, unused_parens, unused_qualifications, unsafe_op_in_unsafe_fn, clippy::all)]
#[path = "gen/notes_store.rs"]
pub mod store;
/// The notes' requests and responses, generated from `Notes.Wire` with the kernel's types and
/// the types the server library generates from `Leangage.Http` and `Leangage.Json`.
#[rustfmt::skip]
#[allow(dead_code, non_snake_case, non_camel_case_types, unused_imports, unused_parens, unused_qualifications, unsafe_op_in_unsafe_fn, clippy::all)]
#[path = "gen/notes_wire.rs"]
pub mod wire;
/// The name `wire` gives the refusal of the guarded kernel.
pub mod authz {
    pub use crate::Refusal as GuardedNotesKernelError;
}

use leanfran::{Local, Owned};
use leangage::http::Api;
use leangage::http_format::{Body, Response};
use leangage::{Kernel, Storage, sql};

pub use generated::notes_kernel as kernel;

/// A refusal of the guarded kernel: the kernel's own (`App`), or the guard's (`Denied`).
pub type Refusal = kernel::LeangageAuthzGuardedNotesKernelError;

pub struct Notes;

impl Kernel for Notes {
    type Principal = kernel::Principal;
    type Snapshot = Owned<kernel::Snapshot>;
    type View = Local<kernel::Snapshot>;
    type Command = kernel::Command;
    type WriteSet = Vec<kernel::Write>;
    type Reply = kernel::Reply;
    type Error = Refusal;

    fn init() -> Owned<kernel::Snapshot> {
        Owned::new(kernel::init())
    }

    fn tenant(actor: &kernel::Principal) -> u64 {
        kernel::tenant(actor.clone())
    }

    fn lend<R>(
        snap: &mut Owned<kernel::Snapshot>,
        f: impl FnOnce(Local<kernel::Snapshot>) -> (Local<kernel::Snapshot>, R),
    ) -> R {
        snap.with(f)
    }

    fn transition(
        actor: &kernel::Principal,
        snap: &Local<kernel::Snapshot>,
        cmd: &kernel::Command,
    ) -> Result<(Vec<kernel::Write>, kernel::Reply), Refusal> {
        kernel::local::transition(actor.clone(), snap, cmd.clone()).get()
    }

    fn apply(snap: Local<kernel::Snapshot>, ws: Vec<kernel::Write>) -> Local<kernel::Snapshot> {
        kernel::local::apply(snap, ws)
    }

    fn read_only(cmd: &kernel::Command) -> bool {
        kernel::read_only(cmd.clone())
    }
}

impl Storage for Notes {
    fn tables() -> Vec<sql::Tab> {
        store::tables()
    }

    fn load(rows: Vec<Vec<Vec<sql::Val>>>) -> Option<Owned<kernel::Snapshot>> {
        store::load(rows).map(Owned::new)
    }

    fn writes(ws: &Vec<kernel::Write>) -> Vec<sql::Write> {
        store::writes(ws.clone())
    }

    /// The body the server sends for the reply.
    fn encode_reply(reply: &kernel::Reply) -> Vec<u8> {
        wire::encode_reply(reply.clone())
    }

    fn decode_reply(bytes: &[u8]) -> Option<kernel::Reply> {
        wire::decode_reply(leangage::json_text::tokens(bytes))
    }
}

/// The name of a refusal in the lines of the differential tests.
pub fn refusal_name(refusal: &Refusal) -> &'static str {
    match refusal {
        Refusal::Denied => "denied",
        Refusal::App {
            e: kernel::Error::NotFound,
        } => "not_found",
        Refusal::App {
            e: kernel::Error::BadText,
        } => "bad_text",
    }
}

impl Api<Notes> for Notes {
    fn request(
        tenant: u64,
        user: u64,
        expiry: u64,
        now: u64,
        body: Body,
    ) -> Result<(kernel::Principal, kernel::Command), Response> {
        wire::request(tenant, user, expiry, now, body).map(|call| (call.actor, call.cmd))
    }

    fn respond(decision: Result<kernel::Reply, Refusal>) -> Response {
        wire::respond(decision)
    }

    fn fingerprint(cmd: &kernel::Command) -> Vec<u8> {
        wire::fingerprint(cmd.clone())
    }

    fn scope(actor: &kernel::Principal) -> String {
        wire::scope(actor.clone())
    }
}
