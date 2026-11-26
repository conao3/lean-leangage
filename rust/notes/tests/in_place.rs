//! The memory engine keeps a tenant's snapshot owned by one thread at a time, so Lean updates
//! it in place, also when commands arrive from several threads and when the guard denies one.

use std::sync::Arc;

use leangage::Engine;
use leangage::memory::MemoryEngine;
use leangage_notes::{Notes, Refusal, kernel};

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn snapshot_stays_owned_by_one_thread() {
    let engine = Arc::new(MemoryEngine::<Notes>::new());
    let mut tasks = Vec::new();
    for user in 0..8_u64 {
        let engine = engine.clone();
        tasks.push(tokio::spawn(async move {
            let actor = kernel::Principal { org: 1, user };
            let mine = (user + 1) * 1000;
            let theirs = ((user + 1) % 8 + 1) * 1000;
            engine
                .execute(
                    actor.clone(),
                    kernel::Command::PutNote {
                        id: mine,
                        body: "first".to_owned(),
                        shared: false,
                    },
                    None,
                )
                .await
                .expect("no engine error")
                .expect("a free id is accepted");
            for arg in 0..200_u64 {
                let cmd = match arg % 4 {
                    0 => kernel::Command::PutNote {
                        id: mine + arg,
                        body: format!("note {arg}"),
                        shared: arg % 8 == 0,
                    },
                    1 => kernel::Command::PutNote {
                        id: mine,
                        body: format!("edit {arg}"),
                        shared: false,
                    },
                    2 => kernel::Command::ReadNote { id: mine },
                    _ => kernel::Command::DeleteNote { id: theirs },
                };
                let result = engine.execute(actor.clone(), cmd, None).await;
                let denied = matches!(result, Ok(Err(Refusal::Denied)));
                if arg % 4 != 3 {
                    assert!(matches!(result, Ok(Ok(_))), "{arg}: {result:?}");
                } else {
                    assert!(denied || matches!(result, Ok(Err(_))), "{arg}: {result:?}");
                }
            }
        }));
    }
    for task in tasks {
        task.await.expect("the task finishes");
    }
    let single = engine
        .inspect(1, |view| unsafe {
            leanfran::runtime::lean_is_st(view.as_obj())
        })
        .expect("the tenant has a snapshot");
    assert!(single);
}
