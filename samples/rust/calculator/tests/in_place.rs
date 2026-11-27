//! The memory engine keeps a tenant's snapshot owned by one thread at a time, so Lean updates
//! it in place, also when commands arrive from several threads and when one is refused.

use std::sync::Arc;

use leangage::Engine;
use leangage::memory::MemoryEngine;
use leangage_calculator::{Calculator, kernel};

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn snapshot_stays_owned_by_one_thread() {
    let engine = Arc::new(MemoryEngine::<Calculator>::new());
    let mut tasks = Vec::new();
    for user in 0..8_u64 {
        let engine = engine.clone();
        tasks.push(tokio::spawn(async move {
            let actor = kernel::Principal { org: 1, user };
            for arg in 0..200_u64 {
                let cmd = match arg % 4 {
                    0 => kernel::Command::Set { value: arg },
                    1 => kernel::Command::Apply {
                        op: kernel::Op::Add,
                        arg,
                    },
                    2 => kernel::Command::Apply {
                        op: kernel::Op::Div,
                        arg: 0,
                    },
                    _ => kernel::Command::Get,
                };
                let refused = matches!(
                    engine.execute(actor.clone(), cmd, None).await,
                    Ok(Err(kernel::Error::DivByZero))
                );
                assert_eq!(refused, arg % 4 == 2);
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
