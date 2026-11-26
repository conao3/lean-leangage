//! axum and tokio-postgres with no kernel: the calculator's table in PostgreSQL, one user's row.
//! `get` reads the row with one `SELECT` in a `SERIALIZABLE READ ONLY DEFERRABLE` transaction;
//! `set` and `apply` with `div` write it with one upsert in a `SERIALIZABLE` transaction, retried
//! after a serialization failure or a deadlock until it commits. It checks no token: every request
//! is the user 7 of the tenant 1. It takes no advisory lock and stores no idempotency key.
use std::time::Duration;

use axum::extract::State;
use axum::http::StatusCode;
use axum::{Json, Router, routing::post};
use deadpool_postgres::{Manager, ManagerConfig, Pool, RecyclingMethod};
use serde_json::{Value, json};
use tokio_postgres::error::SqlState;
use tokio_postgres::{IsolationLevel, NoTls};

/// The connections of the pool, as many as the leangage calculator server's.
const POOL_SIZE: usize = 16;
const TENANT: i64 = 1;
const USER: i64 = 7;
const DDL: &str = "CREATE TABLE IF NOT EXISTS \"memories\" (\"tenant_id\" BIGINT NOT NULL, \
    \"user\" BIGINT NOT NULL, \"value\" BIGINT NOT NULL, PRIMARY KEY (\"tenant_id\", \"user\"))";
const SELECT: &str =
    "SELECT \"value\" FROM \"memories\" WHERE \"tenant_id\" = $1 AND \"user\" = $2";
const SET: &str = "INSERT INTO \"memories\" (\"tenant_id\", \"user\", \"value\") \
    VALUES ($1, $2, $3) ON CONFLICT (\"tenant_id\", \"user\") DO UPDATE SET \"value\" = $3 \
    RETURNING \"value\"";
const DIV: &str = "INSERT INTO \"memories\" (\"tenant_id\", \"user\", \"value\") \
    VALUES ($1, $2, 0) ON CONFLICT (\"tenant_id\", \"user\") \
    DO UPDATE SET \"value\" = \"memories\".\"value\" / $3 RETURNING \"value\"";

enum Statement {
    Read,
    Write(&'static str, i64),
}

fn statement(body: &Value) -> Option<Statement> {
    match body.get("cmd")?.as_str()? {
        "get" => Some(Statement::Read),
        "set" => Some(Statement::Write(SET, body.get("value")?.as_i64()?)),
        "apply" if body.get("op")?.as_str()? == "div" => {
            let arg = body.get("arg")?.as_i64().filter(|&arg| arg != 0)?;
            Some(Statement::Write(DIV, arg))
        }
        _ => None,
    }
}

async fn attempt(pool: &Pool, st: &Statement) -> Result<i64, tokio_postgres::Error> {
    let mut client = pool.get().await.expect("a connection");
    let tx = match st {
        Statement::Read => client
            .build_transaction()
            .isolation_level(IsolationLevel::Serializable)
            .read_only(true)
            .deferrable(true),
        Statement::Write(..) => client
            .build_transaction()
            .isolation_level(IsolationLevel::Serializable),
    }
    .start()
    .await?;
    let value = match st {
        Statement::Read => {
            let q = tx.prepare_cached(SELECT).await?;
            tx.query_opt(&q, &[&TENANT, &USER])
                .await?
                .map_or(0, |row| row.get(0))
        }
        Statement::Write(text, arg) => {
            let q = tx.prepare_cached(text).await?;
            tx.query_one(&q, &[&TENANT, &USER, arg]).await?.get(0)
        }
    };
    tx.commit().await?;
    Ok(value)
}

fn retryable(e: &tokio_postgres::Error) -> bool {
    e.code().is_some_and(|c| {
        *c == SqlState::T_R_SERIALIZATION_FAILURE || *c == SqlState::T_R_DEADLOCK_DETECTED
    })
}

async fn rpc(State(pool): State<Pool>, Json(body): Json<Value>) -> (StatusCode, Json<Value>) {
    let Some(st) = statement(&body) else {
        return (
            StatusCode::UNPROCESSABLE_ENTITY,
            Json(json!({"error": "bad"})),
        );
    };
    for n in 0.. {
        match attempt(&pool, &st).await {
            Ok(value) => return (StatusCode::OK, Json(json!({ "value": value }))),
            Err(e) if retryable(&e) => {
                let nanos = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .map_or(0, |d| d.subsec_nanos());
                let cap_us = 1000u64 << n.min(8);
                tokio::time::sleep(Duration::from_micros(u64::from(nanos) % cap_us + 100)).await;
            }
            Err(e) => {
                return (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    Json(json!({"error": e.to_string()})),
                );
            }
        }
    }
    unreachable!("the attempts are unbounded")
}

#[tokio::main]
async fn main() {
    let listen = std::env::var("BENCH_LISTEN").expect("BENCH_LISTEN");
    let url = std::env::var("BENCH_DATABASE_URL").expect("BENCH_DATABASE_URL");
    let pg: tokio_postgres::Config = url.parse().expect("BENCH_DATABASE_URL");
    let manager = Manager::from_config(
        pg,
        NoTls,
        ManagerConfig {
            recycling_method: RecyclingMethod::Fast,
        },
    );
    let pool = Pool::builder(manager)
        .max_size(POOL_SIZE)
        .build()
        .expect("a pool");
    pool.get()
        .await
        .expect("BENCH_DATABASE_URL connects")
        .batch_execute(DDL)
        .await
        .expect("the table is created");
    let listener = tokio::net::TcpListener::bind(listen).await.expect("bind");
    let router = Router::new().route("/rpc", post(rpc)).with_state(pool);
    axum::serve(listener, router).await.expect("serve");
}
