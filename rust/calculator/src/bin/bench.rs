//! Times one command through the generated kernel, with the snapshot as a Rust value and as a
//! Lean value, and through the memory engine, for tenants of several sizes, next to the same
//! logic written by hand in Rust.

use std::hint::black_box;
use std::time::Instant;

use leanharbor::memory::{Core, MemoryEngine};
use leanharbor::{Engine, Kernel};
use leanharbor_calculator::{Calculator, kernel};

fn handwritten(
    actor: &kernel::Principal,
    snap: &mut Vec<kernel::Memory>,
    cmd: &kernel::Command,
) -> Result<u64, kernel::Error> {
    let slot = snap.iter().position(|m| m.user == actor.user);
    let current = slot.map_or(0, |i| snap[i].value);
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
    match slot {
        Some(i) => snap[i].value = value,
        None => snap.push(kernel::Memory {
            user: actor.user,
            value,
        }),
    }
    Ok(value)
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
    for users in [1_u64, 100, 10_000] {
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
            let (ws, _) = Calculator::transition(actor, &snap, cmd).expect("set is accepted");
            snap = Calculator::apply(snap, ws);
        }
        let start = Instant::now();
        for (actor, cmd) in &cmds {
            if let Ok((ws, reply)) = Calculator::transition(actor, &snap, cmd) {
                black_box(reply);
                snap = Calculator::apply(snap, ws);
            }
        }
        per_op("generated kernel, Lean values", users, count, start);

        let start = Instant::now();
        for (actor, cmd) in &cmds {
            let _ = black_box(Calculator::transition(actor, &snap, cmd));
        }
        per_op("  transition alone", users, count, start);

        let mut core = Core::<Calculator>::new();
        for (actor, cmd) in &seed {
            let _ = core.execute(actor, cmd, None);
        }
        let start = Instant::now();
        for (actor, cmd) in &cmds {
            let _ = black_box(core.execute(actor, cmd, None));
        }
        per_op("memory engine core", users, count, start);

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
            per_op("memory engine, one caller at a time", users, count, start);
        });

        let mut plain = Vec::new();
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
