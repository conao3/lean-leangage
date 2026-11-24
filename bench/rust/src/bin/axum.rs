//! axum with no kernel: decodes the JSON body and replies with a JSON value.

use axum::{Json, Router, routing::post};
use serde_json::{Value, json};

async fn rpc(Json(_): Json<Value>) -> Json<Value> {
    Json(json!({ "value": 6 }))
}

#[tokio::main]
async fn main() {
    let listen = std::env::var("BENCH_LISTEN").expect("BENCH_LISTEN");
    let listener = tokio::net::TcpListener::bind(listen).await.expect("bind");
    axum::serve(listener, Router::new().route("/rpc", post(rpc)))
        .await
        .expect("serve");
}
