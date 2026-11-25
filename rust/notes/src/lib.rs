//! The notes: the kernel is `lean/Notes/Kernel.lean`, generated to `src/generated/`. Its
//! `transition` is the kernel's `handle` behind the guard of `lean/Leanharbor/Authz.lean`.

#[rustfmt::skip]
pub mod generated;

use axum::http::StatusCode;
use leanfran::{Local, Owned};
use leanharbor::Kernel;
use leanharbor::http::Api;
use leanharbor::json_format::{self, StrTok};
use serde::Deserialize;
use serde_json::{Value, json};

pub use generated::notes_kernel as kernel;

/// A refusal of the guarded kernel: the kernel's own (`App`), or the guard's (`Denied`).
pub type Refusal = kernel::LeanharborAuthzGuardedNotesKernelError;

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
}

#[derive(Deserialize)]
#[serde(tag = "cmd", rename_all = "snake_case", deny_unknown_fields)]
enum WireCommand {
    AddMember { user: u64, admin: bool },
    RemoveMember { user: u64 },
    PutNote { id: u64, body: String, shared: bool },
    DeleteNote { id: u64 },
    ReadNote { id: u64 },
    ListNotes,
    ListMembers,
}

fn note(n: &kernel::Note) -> Value {
    json!({ "id": n.id, "owner": n.owner, "shared": n.shared, "body": n.body })
}

fn member(m: &kernel::Member) -> Value {
    json!({ "user": m.user, "admin": m.admin })
}

/// The name of a refusal on the wire.
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

/// The tokens of a JSON value made of objects, arrays, strings, booleans and numbers below 2^64.
fn toks(value: &Value, out: &mut Vec<StrTok>) {
    match value {
        Value::Null => out.push(StrTok::Null),
        Value::Bool(b) => out.push(StrTok::Bool { b: *b }),
        Value::Number(n) => out.push(StrTok::Num {
            n: n.as_u64().expect("the notes write numbers below 2^64"),
        }),
        Value::String(s) => out.push(StrTok::Str { s: s.clone() }),
        Value::Array(items) => {
            out.push(StrTok::ArrOpen);
            items.iter().for_each(|item| toks(item, out));
            out.push(StrTok::ArrClose);
        }
        Value::Object(fields) => {
            out.push(StrTok::ObjOpen);
            for (key, field) in fields {
                out.push(StrTok::Key { s: key.clone() });
                toks(field, out);
            }
            out.push(StrTok::ObjClose);
        }
    }
}

/// The bytes of the value, written by the JSON writer generated from `Leanharbor.Json`.
fn body(value: Value) -> Vec<u8> {
    let mut out = Vec::new();
    toks(&value, &mut out);
    json_format::write_array(out)
}

impl Api<Notes> for Notes {
    fn principal(tenant: u64, user: u64) -> kernel::Principal {
        kernel::Principal { org: tenant, user }
    }

    fn decode_command(body: Value) -> Result<kernel::Command, String> {
        let wire: WireCommand = serde_json::from_value(body).map_err(|e| e.to_string())?;
        Ok(match wire {
            WireCommand::AddMember { user, admin } => kernel::Command::AddMember { user, admin },
            WireCommand::RemoveMember { user } => kernel::Command::RemoveMember { user },
            WireCommand::PutNote { id, body, shared } => {
                kernel::Command::PutNote { id, body, shared }
            }
            WireCommand::DeleteNote { id } => kernel::Command::DeleteNote { id },
            WireCommand::ReadNote { id } => kernel::Command::ReadNote { id },
            WireCommand::ListNotes => kernel::Command::ListNotes,
            WireCommand::ListMembers => kernel::Command::ListMembers,
        })
    }

    fn encode_reply(reply: &kernel::Reply) -> Vec<u8> {
        body(match reply {
            kernel::Reply::Done => json!({ "done": true }),
            kernel::Reply::Found { n } => json!({ "note": note(n) }),
            kernel::Reply::Notes { ns } => {
                json!({ "notes": ns.iter().map(note).collect::<Vec<_>>() })
            }
            kernel::Reply::Members { ms } => {
                json!({ "members": ms.iter().map(member).collect::<Vec<_>>() })
            }
        })
    }

    fn encode_error(error: &Refusal) -> (StatusCode, Vec<u8>) {
        let status = match error {
            Refusal::Denied => StatusCode::FORBIDDEN,
            Refusal::App {
                e: kernel::Error::NotFound,
            } => StatusCode::NOT_FOUND,
            Refusal::App {
                e: kernel::Error::BadText,
            } => StatusCode::UNPROCESSABLE_ENTITY,
        };
        (status, body(json!({ "error": refusal_name(error) })))
    }

    fn fingerprint(cmd: &kernel::Command) -> Vec<u8> {
        format!("{cmd:?}").into_bytes()
    }

    fn scope(actor: &kernel::Principal) -> String {
        format!("u{}", actor.user)
    }
}
