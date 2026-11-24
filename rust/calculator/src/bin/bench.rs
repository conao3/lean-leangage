//! Times one command through the generated kernel and through the memory engine, for tenants
//! of several sizes, next to the same logic written by hand in Rust.

use std::hint::black_box;
use std::time::Instant;

use leanharbor::memory::MemoryEngine;
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

        let mut snap = kernel::init();
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
        per_op("generated transition + apply", users, count, start);

        let start = Instant::now();
        for _ in 0..count {
            black_box(snap.clone());
        }
        per_op("  clone the snapshot", users, count, start);

        let start = Instant::now();
        for _ in 0..count {
            snap = kernel::apply(snap, None);
        }
        per_op("  convert to Lean and back", users, count, start);

        let start = Instant::now();
        for (actor, _) in &cmds {
            black_box(kernel::memory_of(snap.memories.clone(), actor.user));
        }
        per_op("  clone, convert, scan (memory_of)", users, count, start);

        let engine = MemoryEngine::<Calculator>::new();
        for (actor, cmd) in &seed {
            let _ = engine.execute(actor, cmd);
        }
        let start = Instant::now();
        for (actor, cmd) in &cmds {
            let _ = black_box(engine.execute(actor, cmd));
        }
        per_op("memory engine execute", users, count, start);

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
