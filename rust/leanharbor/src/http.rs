//! `POST /rpc`: one kernel command per request.
//!
//! | case | status | body |
//! |---|---|---|
//! | accepted | 200 | the reply |
//! | missing or rejected token | 401 | `{"error": ...}` |
//! | body is not a command | 400 | `{"error": ...}` |
//! | refused by the kernel | chosen by [`Api::encode_error`] | chosen by [`Api::encode_error`] |
//! | idempotency key reused for another command | 422 | `{"error":"idempotency key reused"}` |

use std::marker::PhantomData;
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use axum::Router;
use axum::body::Bytes;
use axum::extract::State;
use axum::http::header::{AUTHORIZATION, CONTENT_TYPE};
use axum::http::{HeaderMap, StatusCode};
use axum::response::{IntoResponse, Response};
use axum::routing::post;
use serde_json::{Value, json};

use crate::{Engine, EngineError, Kernel, token};

/// How a kernel's commands, replies and refusals appear on the wire, and who a token's holder
/// is. Trusted: no theorem covers it.
pub trait Api<K: Kernel>: Send + Sync + 'static {
    fn principal(tenant: u64, user: u64) -> K::Principal;
    fn decode_command(body: Value) -> Result<K::Command, String>;
    fn encode_reply(reply: &K::Reply) -> Value;
    fn encode_error(error: &K::Error) -> (StatusCode, Value);
    /// Identifies the command under an idempotency key.
    fn fingerprint(cmd: &K::Command) -> Vec<u8>;
    /// Separates the idempotency keys of principals of one tenant.
    fn scope(actor: &K::Principal) -> String;
}

struct App<K: Kernel, A, E> {
    engine: Arc<E>,
    secret: Vec<u8>,
    marker: PhantomData<fn() -> (K, A)>,
}

fn reply(status: StatusCode, body: Value) -> Response {
    (
        status,
        [(CONTENT_TYPE, "application/json")],
        body.to_string(),
    )
        .into_response()
}

fn error(status: StatusCode, message: &str) -> Response {
    reply(status, json!({ "error": message }))
}

fn authenticate(secret: &[u8], headers: &HeaderMap) -> Result<token::Claims, &'static str> {
    let header = headers
        .get(AUTHORIZATION)
        .and_then(|v| v.to_str().ok())
        .ok_or("missing authorization header")?;
    let token = header
        .strip_prefix("Bearer ")
        .ok_or("authorization is not a bearer token")?;
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_secs());
    token::verify(secret, token, now).map_err(|e| match e {
        token::TokenError::Malformed => "malformed token",
        token::TokenError::BadSignature => "bad token signature",
        token::TokenError::Expired => "token expired",
    })
}

async fn rpc<K: Kernel, A: Api<K>, E: Engine<K>>(
    State(app): State<Arc<App<K, A, E>>>,
    headers: HeaderMap,
    body: Bytes,
) -> Response {
    let claims = match authenticate(&app.secret, &headers) {
        Ok(claims) => claims,
        Err(message) => return error(StatusCode::UNAUTHORIZED, message),
    };
    let actor = A::principal(claims.tenant, claims.user);
    let value: Value = match serde_json::from_slice(&body) {
        Ok(value) => value,
        Err(e) => return error(StatusCode::BAD_REQUEST, &e.to_string()),
    };
    let cmd = match A::decode_command(value) {
        Ok(cmd) => cmd,
        Err(message) => return error(StatusCode::BAD_REQUEST, &message),
    };
    let key = headers.get("idempotency-key").and_then(|v| v.to_str().ok());
    let executed = match key {
        Some(key) => app.engine.execute_idempotent(
            &actor,
            &A::scope(&actor),
            key,
            &A::fingerprint(&cmd),
            &cmd,
        ),
        None => app.engine.execute(&actor, &cmd),
    };
    match executed {
        Ok(Ok(r)) => reply(StatusCode::OK, A::encode_reply(&r)),
        Ok(Err(e)) => {
            let (status, body) = A::encode_error(&e);
            reply(status, body)
        }
        Err(EngineError::IdempotencyConflict) => {
            error(StatusCode::UNPROCESSABLE_ENTITY, "idempotency key reused")
        }
    }
}

/// A router with `POST /rpc` that authenticates with `secret` and runs commands on `engine`.
pub fn rpc_router<K: Kernel, A: Api<K>, E: Engine<K>>(engine: Arc<E>, secret: Vec<u8>) -> Router {
    let app = Arc::new(App::<K, A, E> {
        engine,
        secret,
        marker: PhantomData,
    });
    Router::new()
        .route("/rpc", post(rpc::<K, A, E>))
        .with_state(app)
}
