use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use axum::Router;
use axum::routing::get;
use leangage::http::rpc_router;
use leangage::memory::MemoryEngine;
use leangage::token::{Claims, issue};
use leangage_calculator::Calculator;
use leangage_pg::{Config, PgEngine, lockdown};

/// Connections of the PostgreSQL engine's pool.
const POOL_SIZE: usize = 16;

fn required(name: &str) -> String {
    std::env::var(name).unwrap_or_else(|_| {
        eprintln!("{name} is required");
        std::process::exit(255)
    })
}

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let secret = required("LEANGAGE_SECRET").into_bytes();
    if let Ok(who) = std::env::var("LEANGAGE_ISSUE") {
        let ids = who
            .split_once(':')
            .and_then(|(org, user)| Some((org.parse::<u64>().ok()?, user.parse::<u64>().ok()?)));
        let Some((tenant, user)) = ids else {
            eprintln!("LEANGAGE_ISSUE must be <org>:<user>");
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
    let database = std::env::var("LEANGAGE_DATABASE_URL").ok();
    if let Ok(roles) = std::env::var("LEANGAGE_LOCKDOWN") {
        let (Some(url), Some((owner, engine))) = (&database, roles.split_once(':')) else {
            eprintln!("LEANGAGE_LOCKDOWN=<owner>:<engine role> needs LEANGAGE_DATABASE_URL");
            std::process::exit(252)
        };
        if let Err(e) = lockdown::<Calculator>(url, owner, engine).await {
            eprintln!("lockdown: {e}");
            std::process::exit(255)
        }
        return Ok(());
    }
    let rpc = match database {
        Some(url) => {
            match PgEngine::<Calculator>::connect(&url, POOL_SIZE, Config::default()).await {
                Ok(engine) => rpc_router::<Calculator, Calculator, _>(Arc::new(engine), secret),
                Err(e) => {
                    eprintln!("LEANGAGE_DATABASE_URL: {e}");
                    std::process::exit(255)
                }
            }
        }
        None => {
            let engine = Arc::new(MemoryEngine::<Calculator>::new());
            rpc_router::<Calculator, Calculator, _>(engine, secret)
        }
    };
    let router = Router::new()
        .route("/healthz", get(|| async { "ok" }))
        .merge(rpc);
    let listener = tokio::net::TcpListener::bind(required("LEANGAGE_LISTEN")).await?;
    axum::serve(listener, router).await
}
