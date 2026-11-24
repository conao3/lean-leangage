"""Times one command through the memory engine for tenants of several sizes."""

import time

from leanharbor import MemoryEngine, Refused

from leanharbor_calculator import KERNEL, kernel


def commands(users: int, count: int) -> list[tuple[kernel.Principal, kernel.Command]]:
    state = 0x9E3779B97F4A7C15
    out = []

    def nxt() -> int:
        nonlocal state
        state ^= (state << 13) & (2**64 - 1)
        state ^= state >> 7
        state ^= (state << 17) & (2**64 - 1)
        return state

    for _ in range(count):
        actor = kernel.Principal(org=1, user=nxt() % users)
        match nxt() % 4:
            case 0:
                cmd = kernel.Command_set(value=nxt() % 1000)
            case 1:
                cmd = kernel.Command_apply(op=kernel.Op.add, arg=nxt() % 1000)
            case 2:
                cmd = kernel.Command_apply(op=kernel.Op.div, arg=1 + nxt() % 9)
            case _:
                cmd = kernel.Command_get()
        out.append((actor, cmd))
    return out


def main() -> None:
    for users, count in [(1, 20_000), (100, 2_000), (1_000, 200), (10_000, 100)]:
        engine = MemoryEngine(KERNEL)
        for user in range(users):
            engine.execute(
                kernel.Principal(org=1, user=user), kernel.Command_set(value=1)
            )
        cmds = commands(users, count)
        start = time.perf_counter_ns()
        for actor, cmd in cmds:
            try:
                engine.execute(actor, cmd)
            except Refused:
                pass
        nanos = (time.perf_counter_ns() - start) / count
        print(
            f"{'memory engine execute':<34} users={users:<6} {nanos:>10.0f} ns/command"
        )


if __name__ == "__main__":
    main()
