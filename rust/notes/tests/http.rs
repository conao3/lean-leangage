//! `POST /rpc` of the notes server: the guard's refusals are 403, the kernel's are 404 and 422.

use std::sync::Arc;

use axum::Router;
use axum::body::{Body, to_bytes};
use axum::http::{Request, StatusCode};
use leanharbor::http::rpc_router;
use leanharbor::memory::MemoryEngine;
use leanharbor::token::{Claims, issue};
use leanharbor_notes::Notes;
use serde_json::{Value, json};
use tower::ServiceExt;

const SECRET: &[u8] = b"secret";

async fn post(router: &Router, user: u64, body: Value) -> (StatusCode, Value) {
    let token = issue(
        SECRET,
        Claims {
            tenant: 1,
            user,
            expiry: 1 << 62,
        },
    );
    let request = Request::post("/rpc")
        .header("authorization", format!("Bearer {token}"))
        .body(Body::from(body.to_string()))
        .expect("a request");
    let response = router.clone().oneshot(request).await.expect("a response");
    let status = response.status();
    let bytes = to_bytes(response.into_body(), 1 << 20)
        .await
        .expect("a body");
    (status, serde_json::from_slice(&bytes).expect("JSON"))
}

#[tokio::test]
async fn refusals_have_their_status() {
    let engine = Arc::new(MemoryEngine::<Notes>::new());
    let router = rpc_router::<Notes, Notes, _>(engine, SECRET.to_vec());
    let note = |id: u64, owner: u64, shared: bool, body: &str| json!({ "id": id, "owner": owner, "shared": shared, "body": body });
    let steps: Vec<(u64, Value, StatusCode, Value)> = vec![
        (
            1,
            json!({"cmd": "add_member", "user": 1, "admin": true}),
            StatusCode::OK,
            json!({"done": true}),
        ),
        (
            1,
            json!({"cmd": "put_note", "id": 7, "body": "draft", "shared": false}),
            StatusCode::OK,
            json!({"done": true}),
        ),
        (
            2,
            json!({"cmd": "put_note", "id": 7, "body": "mine", "shared": true}),
            StatusCode::FORBIDDEN,
            json!({"error": "denied"}),
        ),
        (
            2,
            json!({"cmd": "delete_note", "id": 7}),
            StatusCode::FORBIDDEN,
            json!({"error": "denied"}),
        ),
        (
            2,
            json!({"cmd": "add_member", "user": 2, "admin": true}),
            StatusCode::FORBIDDEN,
            json!({"error": "denied"}),
        ),
        (
            2,
            json!({"cmd": "read_note", "id": 7}),
            StatusCode::NOT_FOUND,
            json!({"error": "not_found"}),
        ),
        (
            2,
            json!({"cmd": "list_notes"}),
            StatusCode::OK,
            json!({"notes": []}),
        ),
        (
            2,
            json!({"cmd": "put_note", "id": 8, "body": "", "shared": true}),
            StatusCode::UNPROCESSABLE_ENTITY,
            json!({"error": "bad_text"}),
        ),
        (
            1,
            json!({"cmd": "put_note", "id": 7, "body": "for everyone", "shared": true}),
            StatusCode::OK,
            json!({"done": true}),
        ),
        (
            2,
            json!({"cmd": "read_note", "id": 7}),
            StatusCode::OK,
            json!({"note": note(7, 1, true, "for everyone")}),
        ),
        (
            2,
            json!({"cmd": "put_note", "id": 8, "body": "ノート", "shared": false}),
            StatusCode::OK,
            json!({"done": true}),
        ),
        (
            1,
            json!({"cmd": "list_notes"}),
            StatusCode::OK,
            json!({"notes": [note(7, 1, true, "for everyone"), note(8, 2, false, "ノート")]}),
        ),
        (
            1,
            json!({"cmd": "add_member", "user": 2, "admin": false}),
            StatusCode::OK,
            json!({"done": true}),
        ),
        (
            2,
            json!({"cmd": "list_members"}),
            StatusCode::OK,
            json!({"members": [{"user": 2, "admin": false}]}),
        ),
        (
            1,
            json!({"cmd": "delete_note", "id": 8}),
            StatusCode::OK,
            json!({"done": true}),
        ),
        (
            1,
            json!({"cmd": "remove_member", "user": 3}),
            StatusCode::NOT_FOUND,
            json!({"error": "not_found"}),
        ),
        (
            1,
            json!({"cmd": "read_note", "id": 7, "body": "x"}),
            StatusCode::BAD_REQUEST,
            json!({"error": "unknown field `body`, expected `id`"}),
        ),
    ];
    for (i, (user, body, status, want)) in steps.into_iter().enumerate() {
        let (got_status, got) = post(&router, user, body).await;
        assert_eq!((got_status, got), (status, want), "step {}", i + 1);
    }
}
