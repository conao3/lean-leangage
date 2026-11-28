//! The calculator: the kernel is `samples/lean/Calculator/Kernel.lean`, its table
//! `samples/lean/Calculator/Store.lean` and its requests and responses
//! `samples/lean/Calculator/Wire.lean`, all generated to `src/gen/`. [`Api`] passes each call on to
//! `wire`.

#[rustfmt::skip]
#[path = "gen/mod.rs"]
pub mod generated;

use leanfran::{Local, Owned};
use leangage::http::Api;
use leangage::http_format::{Body, Response};
use leangage::{Kernel, Storage, sql};

pub use generated::calculator_kernel as kernel;
pub use generated::calculator_store as store;
pub use generated::calculator_wire as wire;

pub struct Calculator;

impl Kernel for Calculator {
    type Principal = kernel::Principal;
    type Snapshot = Owned<kernel::Snapshot>;
    type View = Local<kernel::Snapshot>;
    type Command = kernel::Command;
    type WriteSet = Option<kernel::Memory>;
    type Reply = kernel::Reply;
    type Error = kernel::Error;

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
    ) -> Result<(Option<kernel::Memory>, kernel::Reply), kernel::Error> {
        kernel::local::transition(actor.clone(), snap, cmd.clone()).get()
    }

    fn apply(snap: Local<kernel::Snapshot>, ws: Option<kernel::Memory>) -> Local<kernel::Snapshot> {
        kernel::local::apply(snap, ws)
    }

    fn read_only(cmd: &kernel::Command) -> bool {
        kernel::read_only(cmd.clone())
    }
}

impl Storage for Calculator {
    fn tables() -> Vec<sql::Tab> {
        store::tables()
    }

    fn load(rows: Vec<Vec<Vec<sql::Val>>>) -> Option<Owned<kernel::Snapshot>> {
        store::load(rows).map(Owned::new)
    }

    fn writes(ws: &Option<kernel::Memory>) -> Vec<sql::Write> {
        store::writes(ws.clone())
    }

    fn encode_reply(reply: &kernel::Reply) -> Vec<u8> {
        reply.v.to_be_bytes().to_vec()
    }

    fn decode_reply(bytes: &[u8]) -> Option<kernel::Reply> {
        let v = u64::from_be_bytes(bytes.try_into().ok()?);
        Some(kernel::Reply { v })
    }
}

impl Api<Calculator> for Calculator {
    fn request(
        tenant: u64,
        user: u64,
        expiry: u64,
        now: u64,
        body: Body,
    ) -> Result<(kernel::Principal, kernel::Command), Response> {
        wire::request(tenant, user, expiry, now, body).map(|call| (call.actor, call.cmd))
    }

    fn respond(decision: Result<kernel::Reply, kernel::Error>) -> Response {
        wire::respond(decision)
    }

    fn fingerprint(cmd: &kernel::Command) -> Vec<u8> {
        wire::fingerprint(cmd.clone())
    }

    fn scope(actor: &kernel::Principal) -> String {
        wire::scope(actor.clone())
    }
}
