//! `POST /rpc`: one kernel command per request.
//!
//! The handler passes the request to generated functions and sends what they return. It reads the
//! `Authorization` header and gives it to [`token::Verifier::admit`], which calls
//! [`crate::http_format::authenticate`] and checks the tag; it gives the claims, the time and the
//! body to [`Api::request`]; it runs the command on the engine; and it gives the kernel's
//! decision to [`Api::respond`] and a failure of the engine to
//! [`crate::http_format::failed`]. The status and the body of every answer come from those
//! functions, which are generated from `lean/Leangage/Http.lean` and from the kernel's module
//! beside it (`lean/Calculator/Wire.lean`).

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

use crate::http_format::{self, Body, Failure};
use crate::json_text;
use crate::{Engine, EngineError, Idempotency, Kernel, token};

/// A kernel's functions on the wire, implemented by delegating to functions generated from Lean.
pub trait Api<K: Kernel>: Send + Sync + 'static {
    /// What the engine runs for a request whose token, checked, claims `tenant`, `user` and
    /// `expiry`, at the time `now`; or the answer to the request.
    fn request(
        tenant: u64,
        user: u64,
        expiry: u64,
        now: u64,
        body: Body,
    ) -> Result<(K::Principal, K::Command), http_format::Response>;
    /// The answer to a command the kernel accepted or refused.
    fn respond(decision: Result<K::Reply, K::Error>) -> http_format::Response;
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

/// Sends a generated answer.
pub fn send(answer: http_format::Response) -> Response {
    let status = StatusCode::from_u16(answer.status).expect("a generated status is a status code");
    (status, [(CONTENT_TYPE, "application/json")], answer.body).into_response()
}

/// The failure a generated answer is made of.
pub fn failure(error: &EngineError) -> Failure {
    match error {
        EngineError::IdempotencyConflict => Failure::Conflict,
        EngineError::Stopped => Failure::Stopped,
        EngineError::RetriesExhausted => Failure::RetriesExhausted,
        EngineError::Database(_) => Failure::Database,
        EngineError::CommitUnknown => Failure::CommitUnknown,
        EngineError::Broken(_) => Failure::Broken,
    }
}

/// The body as the generated functions take it.
pub fn body_of(bytes: &[u8]) -> Body {
    match json_text::lexemes(bytes) {
        Some(lexemes) => Body::Json { lexemes },
        None => Body::NotJson,
    }
}

/// Seconds since the Unix epoch.
pub fn now() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_secs())
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
    let (actor, cmd) = match A::request(
        claims.tenant,
        claims.user,
        claims.expiry,
        now(),
        body_of(&body),
    ) {
        Ok(call) => call,
        Err(answer) => return send(answer),
    };
    let idempotency = headers
        .get("idempotency-key")
        .and_then(|v| v.to_str().ok())
        .map(|key| Idempotency {
            scope: A::scope(&actor),
            key: key.to_owned(),
            fingerprint: A::fingerprint(&cmd),
        });
    match app.engine.execute(actor, cmd, idempotency).await {
        Ok(decision) => send(A::respond(decision)),
        Err(error) => send(http_format::failed(failure(&error))),
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
