//! `POST /rpc` of the calculator: the status and the body of each answer.

use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use axum::body::{Body, to_bytes};
use axum::http::{Request, StatusCode};
use leangage::http::rpc_router;
use leangage::memory::MemoryEngine;
use leangage::token::{Claims, issue};
use leangage_calculator::Calculator;
use tower::ServiceExt;

const SECRET: &[u8] = b"secret";

/// The `Authorization` header, the idempotency key, the body, and the status and the body of
/// the answer.
type Step = (
    Option<String>,
    Option<&'static str>,
    &'static str,
    u16,
    &'static str,
);

fn token(secret: &[u8], user: u64, expiry: u64) -> String {
    issue(
        secret,
        Claims {
            tenant: 1,
            user,
            expiry,
        },
    )
}

async fn post(
    router: &axum::Router,
    authorization: Option<String>,
    key: Option<&str>,
    body: Vec<u8>,
) -> (StatusCode, String) {
    let mut request = Request::post("/rpc");
    if let Some(authorization) = authorization {
        request = request.header("authorization", authorization);
    }
    if let Some(key) = key {
        request = request.header("idempotency-key", key);
    }
    let response = router
        .clone()
        .oneshot(request.body(Body::from(body)).expect("a request"))
        .await
        .expect("the router answers");
    let status = response.status();
    assert_eq!(
        response.headers().get("content-type").map(|v| v.as_bytes()),
        Some(&b"application/json"[..])
    );
    let bytes = to_bytes(response.into_body(), usize::MAX)
        .await
        .expect("a body");
    (status, String::from_utf8(bytes.to_vec()).expect("UTF-8"))
}

#[tokio::test]
async fn statuses_and_bodies() {
    let router = rpc_router::<Calculator, Calculator, _>(
        Arc::new(MemoryEngine::<Calculator>::new()),
        SECRET.to_vec(),
    );
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("after 1970")
        .as_secs();
    let good = format!("Bearer {}", token(SECRET, 7, now + 600));
    let steps: Vec<Step> = vec![
        (
            None,
            None,
            "{",
            401,
            r#"{"error":"missing authorization header"}"#,
        ),
        (
            Some(format!("Basic {}", token(SECRET, 7, now + 600))),
            None,
            "{",
            401,
            r#"{"error":"authorization is not a bearer token"}"#,
        ),
        (
            Some("Bearer v1.1.1".to_owned()),
            None,
            "{",
            401,
            r#"{"error":"malformed token"}"#,
        ),
        (
            Some(format!("Bearer {}", token(b"other", 7, now + 600))),
            None,
            "{",
            401,
            r#"{"error":"bad token signature"}"#,
        ),
        (
            Some(format!("Bearer {}", token(b"other", 7, 1))),
            None,
            "{",
            401,
            r#"{"error":"bad token signature"}"#,
        ),
        (
            Some(format!("Bearer {}", token(SECRET, 7, 1))),
            None,
            "{",
            401,
            r#"{"error":"token expired"}"#,
        ),
        (
            Some(good.clone()),
            None,
            r#"{"cmd":"set","value":6}"#,
            200,
            r#"{"value":6}"#,
        ),
        (
            Some(good.clone()),
            None,
            r#" { "value" : 7 , "cmd" : "set" } "#,
            200,
            r#"{"value":7}"#,
        ),
        (
            Some(good.clone()),
            None,
            r#"{"cmd":"apply","op":"mul","arg":6}"#,
            200,
            r#"{"value":42}"#,
        ),
        (
            Some(good.clone()),
            None,
            r#"{"cmd":"get"}"#,
            200,
            r#"{"value":42}"#,
        ),
        (
            Some(good.clone()),
            None,
            r#"{"cmd":"apply","op":"div","arg":0}"#,
            422,
            r#"{"error":"division_by_zero"}"#,
        ),
        (
            Some(good.clone()),
            None,
            r#"{"cmd":"apply","op":"mul","arg":18446744073709551615}"#,
            422,
            r#"{"error":"overflow"}"#,
        ),
        (
            Some(good.clone()),
            Some("k"),
            r#"{"cmd":"apply","op":"add","arg":1}"#,
            200,
            r#"{"value":43}"#,
        ),
        (
            Some(good.clone()),
            Some("k"),
            r#"{"cmd":"apply","op":"add","arg":1}"#,
            200,
            r#"{"value":43}"#,
        ),
        (
            Some(good.clone()),
            Some("k"),
            r#"{"cmd":"apply","op":"add","arg":2}"#,
            422,
            r#"{"error":"idempotency key reused"}"#,
        ),
        (
            Some(good.clone()),
            None,
            "{",
            400,
            r#"{"error":"body is not JSON"}"#,
        ),
        (
            Some(good.clone()),
            None,
            r#"{"cmd":"get"} x"#,
            400,
            r#"{"error":"body is not JSON"}"#,
        ),
        (
            Some(good.clone()),
            None,
            "",
            400,
            r#"{"error":"body is not JSON"}"#,
        ),
        (
            Some(good.clone()),
            None,
            r#"{"cmd":"set"}"#,
            400,
            r#"{"error":"not a calculator command"}"#,
        ),
        (
            Some(good.clone()),
            None,
            r#"{"cmd":"set","value":6,"arg":1}"#,
            400,
            r#"{"error":"not a calculator command"}"#,
        ),
        (
            Some(good.clone()),
            None,
            r#"{"cmd":"get","cmd":"get"}"#,
            400,
            r#"{"error":"not a calculator command"}"#,
        ),
        (
            Some(good.clone()),
            None,
            r#"{"cmd":"apply","op":"pow","arg":1}"#,
            400,
            r#"{"error":"not a calculator command"}"#,
        ),
        (
            Some(good.clone()),
            None,
            "[]",
            400,
            r#"{"error":"not a calculator command"}"#,
        ),
        (
            Some(good.clone()),
            None,
            r#"{"CMD":"get"}"#,
            400,
            r#"{"error":"missing field `cmd`"}"#,
        ),
        (
            Some(good.clone()),
            None,
            r#"{"cmd":"set","value":6.0}"#,
            400,
            r#"{"error":"`value` must be an integer below 2^64"}"#,
        ),
        (
            Some(good.clone()),
            None,
            r#"{"cmd":"set","value":18446744073709551616}"#,
            400,
            r#"{"error":"`value` must be an integer below 2^64"}"#,
        ),
        (
            Some(good.clone()),
            None,
            r#"{"cmd":"apply","op":"add","arg":-1}"#,
            400,
            r#"{"error":"`arg` must be an integer below 2^64"}"#,
        ),
    ];
    for (i, (authorization, key, body, status, want)) in steps.into_iter().enumerate() {
        let (got_status, got) = post(&router, authorization, key, body.as_bytes().to_vec()).await;
        assert_eq!(
            (got_status.as_u16(), got.as_str()),
            (status, want),
            "step {}",
            i + 1
        );
    }
    let (status, body) = post(&router, Some(good.clone()), None, vec![0xff, 0xfe]).await;
    assert_eq!(
        (status.as_u16(), body.as_str()),
        (400, r#"{"error":"body is not JSON"}"#)
    );
}

/// A body of nothing but `[`, as long as the route reads, is answered and not a crash.
#[tokio::test]
async fn a_deep_body_is_refused() {
    let router = rpc_router::<Calculator, Calculator, _>(
        Arc::new(MemoryEngine::<Calculator>::new()),
        SECRET.to_vec(),
    );
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("after 1970")
        .as_secs();
    let good = format!("Bearer {}", token(SECRET, 7, now + 600));
    let deep = vec![b'['; 2 * 1024 * 1024 - 1];
    let (status, body) = post(&router, Some(good.clone()), None, deep).await;
    assert_eq!(
        (status.as_u16(), body.as_str()),
        (400, r#"{"error":"body is not JSON"}"#)
    );
    let mut nested = vec![b'['; 500_000];
    nested.extend(vec![b']'; 500_000]);
    let (status, body) = post(&router, Some(good), None, nested).await;
    assert_eq!(
        (status.as_u16(), body.as_str()),
        (400, r#"{"error":"not a calculator command"}"#)
    );
}
