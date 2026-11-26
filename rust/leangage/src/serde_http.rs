//! `POST /rpc` for a kernel whose commands and replies are read and written with serde_json: one
//! kernel command per request. The notes server uses it.
//!
//! | case | status | body |
//! |---|---|---|
//! | accepted | 200 | the reply |
//! | missing or rejected token | 401 | `{"error": ...}` |
//! | body is not a command | 400 | `{"error": ...}` |
//! | refused by the kernel | chosen by [`Api::encode_error`] | chosen by [`Api::encode_error`] |
//! | a failure of the engine | chosen by [`crate::http_format::failed`] | `{"error": ...}` |
//!
//! The token is read by [`token::Verifier::admit`], its expiry is checked by
//! [`crate::http_format::admit`] and the failures of the engine are answered by
//! [`crate::http_format::failed`], all generated from `lean/Leangage/Http.lean`. The body is
//! decoded by serde_json and [`Api::decode_command`], written by hand.

use std::marker::PhantomData;
use std::sync::Arc;

use axum::Router;
use axum::body::Bytes;
use axum::extract::State;
use axum::http::header::AUTHORIZATION;
use axum::http::{HeaderMap, StatusCode};
use axum::response::Response;
use axum::routing::post;
use serde_json::Value;

use crate::http::{body_of, failure, now, send};
use crate::http_format;
use crate::{Engine, Idempotency, Kernel, token};

/// How a kernel's commands, replies and refusals appear on the wire, and who a token's holder
/// is. Trusted: no theorem covers it. `encode_reply` and `encode_error` return the bytes of the
/// body.
pub trait Api<K: Kernel>: Send + Sync + 'static {
    fn principal(tenant: u64, user: u64) -> K::Principal;
    fn decode_command(body: Value) -> Result<K::Command, String>;
    fn encode_reply(reply: &K::Reply) -> Vec<u8>;
    fn encode_error(error: &K::Error) -> (StatusCode, Vec<u8>);
    /// Identifies the command under an idempotency key.
    fn fingerprint(cmd: &K::Command) -> Vec<u8>;
    /// Separates the idempotency keys of principals of one tenant.
    fn scope(actor: &K::Principal) -> String;
}

struct App<K: Kernel, A, E> {
    engine: Arc<E>,
    verifier: token::Verifier,
    marker: PhantomData<fn() -> (K, A)>,
}

fn reply(status: StatusCode, body: Vec<u8>) -> Response {
    send(http_format::Response {
        status: status.as_u16(),
        body,
    })
}

fn error(status: StatusCode, message: &str) -> Response {
    send(http_format::refuse(status.as_u16(), message))
}

async fn rpc<K: Kernel, A: Api<K>, E: Engine<K>>(
    State(app): State<Arc<App<K, A, E>>>,
    headers: HeaderMap,
    body: Bytes,
) -> Response {
    let authorization = headers.get(AUTHORIZATION).and_then(|v| v.to_str().ok());
    let claims = match app.verifier.admit(authorization) {
        Ok(claims) => claims,
        Err(answer) => return send(answer),
    };
    let text = match http_format::admit(claims.expiry, now(), body_of(&body)) {
        Ok(text) => text,
        Err(answer) => return send(answer),
    };
    let actor = A::principal(claims.tenant, claims.user);
    let value: Value = match serde_json::from_str(&text) {
        Ok(value) => value,
        Err(e) => return error(StatusCode::BAD_REQUEST, &e.to_string()),
    };
    let cmd = match A::decode_command(value) {
        Ok(cmd) => cmd,
        Err(message) => return error(StatusCode::BAD_REQUEST, &message),
    };
    let idempotency = headers
        .get("idempotency-key")
        .and_then(|v| v.to_str().ok())
        .map(|key| Idempotency {
            scope: A::scope(&actor),
            key: key.to_owned(),
            fingerprint: A::fingerprint(&cmd),
        });
    let executed = app.engine.execute(actor, cmd, idempotency).await;
    match executed {
        Ok(Ok(r)) => reply(StatusCode::OK, A::encode_reply(&r)),
        Ok(Err(e)) => {
            let (status, body) = A::encode_error(&e);
            reply(status, body)
        }
        Err(e) => send(http_format::failed(failure(&e))),
    }
}

/// A router with `POST /rpc` that authenticates with `secret` and runs commands on `engine`.
pub fn rpc_router<K: Kernel, A: Api<K>, E: Engine<K>>(engine: Arc<E>, secret: Vec<u8>) -> Router {
    let app = Arc::new(App::<K, A, E> {
        engine,
        verifier: token::Verifier::new(secret),
        marker: PhantomData,
    });
    Router::new()
        .route("/rpc", post(rpc::<K, A, E>))
        .with_state(app)
}
