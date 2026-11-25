//! The calculator: the kernel is `lean/Calculator/Kernel.lean` and its table
//! `lean/Calculator/Store.lean`, both generated to `src/generated/`.

#[rustfmt::skip]
pub mod generated;
/// The calculator's table, generated from `Calculator.Store` with the kernel's types and the
/// types of `leanharbor::sql`.
#[rustfmt::skip]
#[allow(dead_code, non_snake_case, non_camel_case_types, unused_imports, unused_parens, unused_qualifications, unsafe_op_in_unsafe_fn, clippy::all)]
#[path = "generated/calculator_store.rs"]
pub mod store;

use axum::http::StatusCode;
use leanfran::{Local, Owned};
use leanharbor::http::Api;
use leanharbor::{Kernel, Storage, sql};
use serde::Deserialize;
use serde_json::Value;

pub use generated::calculator_kernel as kernel;

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

    fn writes(ws: Option<kernel::Memory>) -> Vec<sql::Write> {
        store::writes(ws)
    }

    fn encode_reply(reply: &kernel::Reply) -> Vec<u8> {
        reply.v.to_be_bytes().to_vec()
    }

    fn decode_reply(bytes: &[u8]) -> Option<kernel::Reply> {
        let v = u64::from_be_bytes(bytes.try_into().ok()?);
        Some(kernel::Reply { v })
    }
}

#[derive(Deserialize)]
#[serde(rename_all = "snake_case")]
enum WireOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Deserialize)]
#[serde(tag = "cmd", rename_all = "snake_case", deny_unknown_fields)]
enum WireCommand {
    Set { value: u64 },
    Apply { op: WireOp, arg: u64 },
    Get,
}

impl Api<Calculator> for Calculator {
    fn principal(tenant: u64, user: u64) -> kernel::Principal {
        kernel::Principal { org: tenant, user }
    }

    fn decode_command(body: Value) -> Result<kernel::Command, String> {
        let wire: WireCommand = serde_json::from_value(body).map_err(|e| e.to_string())?;
        Ok(match wire {
            WireCommand::Set { value } => kernel::Command::Set { value },
            WireCommand::Apply { op, arg } => kernel::Command::Apply {
                op: match op {
                    WireOp::Add => kernel::Op::Add,
                    WireOp::Sub => kernel::Op::Sub,
                    WireOp::Mul => kernel::Op::Mul,
                    WireOp::Div => kernel::Op::Div,
                },
                arg,
            },
            WireCommand::Get => kernel::Command::Get,
        })
    }

    fn encode_reply(reply: &kernel::Reply) -> Vec<u8> {
        kernel::encode_reply(reply.clone())
    }

    fn encode_error(error: &kernel::Error) -> (StatusCode, Vec<u8>) {
        (
            StatusCode::UNPROCESSABLE_ENTITY,
            kernel::encode_error(*error),
        )
    }

    fn fingerprint(cmd: &kernel::Command) -> Vec<u8> {
        format!("{cmd:?}").into_bytes()
    }

    fn scope(actor: &kernel::Principal) -> String {
        format!("u{}", actor.user)
    }
}
