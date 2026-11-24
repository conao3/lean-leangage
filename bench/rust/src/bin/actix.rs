//! actix-web with no kernel: decodes the JSON body and replies with a JSON value.

use actix_web::{App, HttpResponse, HttpServer, web};
use serde_json::{Value, json};

async fn rpc(_: web::Json<Value>) -> HttpResponse {
    HttpResponse::Ok().json(json!({ "value": 6 }))
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    let listen = std::env::var("BENCH_LISTEN").expect("BENCH_LISTEN");
    HttpServer::new(|| App::new().route("/rpc", web::post().to(rpc)))
        .bind(listen)?
        .run()
        .await
}
