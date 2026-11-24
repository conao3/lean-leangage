use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use axum::Router;
use axum::routing::get;
use leanharbor::http::rpc_router;
use leanharbor::memory::MemoryEngine;
use leanharbor::token::{Claims, issue};
use leanharbor_calculator::Calculator;

fn required(name: &str) -> String {
    std::env::var(name).unwrap_or_else(|_| {
        eprintln!("{name} is required");
        std::process::exit(255)
    })
}

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let secret = required("LEANHARBOR_SECRET").into_bytes();
    if let Ok(who) = std::env::var("LEANHARBOR_ISSUE") {
        let ids = who
            .split_once(':')
            .and_then(|(org, user)| Some((org.parse::<u64>().ok()?, user.parse::<u64>().ok()?)));
        let Some((tenant, user)) = ids else {
            eprintln!("LEANHARBOR_ISSUE must be <org>:<user>");
            std::process::exit(252)
        };
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| d.as_secs());
        let claims = Claims {
            tenant,
            user,
            expiry: now + 86_400,
        };
        println!("{}", issue(&secret, claims));
        return Ok(());
    }
    let engine = Arc::new(MemoryEngine::<Calculator>::new());
    let router = Router::new()
        .route("/healthz", get(|| async { "ok" }))
        .merge(rpc_router::<Calculator, Calculator, _>(engine, secret));
    let listener = tokio::net::TcpListener::bind(required("LEANHARBOR_LISTEN")).await?;
    axum::serve(listener, router).await
}
