//! Times one command through the generated kernel, with the snapshot as a Rust value and as a
//! Lean value, and through the memory engine, for tenants of several sizes, next to the same
//! commands on a `HashMap` written by hand in Rust. With `LEANHARBOR_DATABASE_URL`, also through
//! the PostgreSQL engine on that database, one tenant per size.

use std::collections::HashMap;
use std::hint::black_box;
use std::time::Instant;

use leanharbor::memory::MemoryEngine;
use leanharbor::{Engine, Kernel};
use leanharbor_calculator::{Calculator, kernel};
use leanharbor_pg::{Config, PgEngine};

fn handwritten(
    actor: &kernel::Principal,
    snap: &mut HashMap<u64, u64>,
    cmd: &kernel::Command,
) -> Result<u64, kernel::Error> {
    let current = snap.get(&actor.user).copied().unwrap_or(0);
    let value = match cmd {
        kernel::Command::Set { value } => *value,
        kernel::Command::Apply { op, arg } => match op {
            kernel::Op::Add => current.checked_add(*arg).ok_or(kernel::Error::Overflow)?,
            kernel::Op::Sub => current.checked_sub(*arg).ok_or(kernel::Error::Underflow)?,
            kernel::Op::Mul => current.checked_mul(*arg).ok_or(kernel::Error::Overflow)?,
            kernel::Op::Div => current.checked_div(*arg).ok_or(kernel::Error::DivByZero)?,
        },
        kernel::Command::Get => return Ok(current),
    };
    snap.insert(actor.user, value);
    Ok(value)
}

fn run(
    snap: &mut <Calculator as Kernel>::Snapshot,
    actor: &kernel::Principal,
    cmd: &kernel::Command,
) -> Result<kernel::Reply, kernel::Error> {
    Calculator::lend(snap, |view| {
        match Calculator::transition(actor, &view, cmd) {
            Ok((ws, reply)) => (Calculator::apply(view, ws), Ok(reply)),
            Err(e) => (view, Err(e)),
        }
    })
}

fn commands(users: u64, count: usize) -> Vec<(kernel::Principal, kernel::Command)> {
    let mut state = 0x9e37_79b9_7f4a_7c15_u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    (0..count)
        .map(|_| {
            let actor = kernel::Principal {
                org: 1,
                user: next() % users,
            };
            let cmd = match next() % 4 {
                0 => kernel::Command::Set {
                    value: next() % 1000,
                },
                1 => kernel::Command::Apply {
                    op: kernel::Op::Add,
                    arg: next() % 1000,
                },
                2 => kernel::Command::Apply {
                    op: kernel::Op::Div,
                    arg: 1 + next() % 9,
                },
                _ => kernel::Command::Get,
            };
            (actor, cmd)
        })
        .collect()
}

fn per_op(label: &str, users: u64, count: usize, start: Instant) {
    let nanos = start.elapsed().as_nanos() as f64 / count as f64;
    println!("{label:<36} users={users:<6} {nanos:>10.0} ns/command");
}

fn main() {
    for users in [1_u64, 100, 1_000, 10_000] {
        let count = if users == 10_000 { 2_000 } else { 200_000 };
        let seed: Vec<_> = (0..users)
            .map(|user| {
                (
                    kernel::Principal { org: 1, user },
                    kernel::Command::Set { value: 1 },
                )
            })
            .collect();
        let cmds = commands(users, count);

        let mut values = kernel::init();
        for (actor, cmd) in &seed {
            let (ws, _) = kernel::transition(actor.clone(), values.clone(), cmd.clone())
                .expect("set is accepted");
            values = kernel::apply(values, ws);
        }
        let start = Instant::now();
        for (actor, cmd) in &cmds {
            if let Ok((ws, reply)) = kernel::transition(actor.clone(), values.clone(), cmd.clone())
            {
                black_box(reply);
                values = kernel::apply(values, ws);
            }
        }
        per_op("generated kernel, Rust values", users, count, start);

        let mut snap = Calculator::init();
        for (actor, cmd) in &seed {
            run(&mut snap, actor, cmd).expect("set is accepted");
        }
        let start = Instant::now();
        for (actor, cmd) in &cmds {
            let _ = black_box(run(&mut snap, actor, cmd));
        }
        per_op("generated kernel, Lean values", users, count, start);

        let start = Instant::now();
        Calculator::lend(&mut snap, |view| {
            for (actor, cmd) in &cmds {
                let _ = black_box(Calculator::transition(actor, &view, cmd));
            }
            (view, ())
        });
        per_op("  transition alone", users, count, start);

        let engine = MemoryEngine::<Calculator>::new();
        let runtime = tokio::runtime::Builder::new_current_thread()
            .build()
            .expect("a runtime");
        runtime.block_on(async {
            for (actor, cmd) in &seed {
                let _ = engine.execute(actor.clone(), cmd.clone(), None).await;
            }
            let start = Instant::now();
            for (actor, cmd) in &cmds {
                let _ = black_box(engine.execute(actor.clone(), cmd.clone(), None).await);
            }
            per_op("memory engine", users, count, start);
        });

        if let Ok(url) = std::env::var("LEANHARBOR_DATABASE_URL") {
            let count = if users >= 1_000 { 200 } else { 2_000 };
            let runtime = tokio::runtime::Builder::new_multi_thread()
                .enable_all()
                .build()
                .expect("a runtime");
            runtime.block_on(async {
                let engine = PgEngine::<Calculator>::connect(&url, 1, Config::default())
                    .await
                    .expect("the engine connects");
                let tenant = |actor: &kernel::Principal| kernel::Principal {
                    org: users,
                    user: actor.user,
                };
                for (actor, cmd) in &seed {
                    engine
                        .execute(tenant(actor), cmd.clone(), None)
                        .await
                        .expect("the engine stores the seed")
                        .expect("set is accepted");
                }
                let start = Instant::now();
                for (actor, cmd) in &cmds[..count] {
                    let decided = engine.execute(tenant(actor), cmd.clone(), None).await;
                    let _ = black_box(decided.expect("the engine runs the command"));
                }
                per_op("postgres engine", users, count, start);
            });
        }

        let mut plain = HashMap::new();
        for (actor, cmd) in &seed {
            let _ = handwritten(actor, &mut plain, cmd);
        }
        let start = Instant::now();
        for (actor, cmd) in &cmds {
            let _ = black_box(handwritten(actor, &mut plain, cmd));
        }
        per_op("handwritten Rust (not proved)", users, count, start);
    }
}
