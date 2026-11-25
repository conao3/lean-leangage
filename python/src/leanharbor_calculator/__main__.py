import os
import sys
import time

from leanharbor import Claims, Engine, EngineError, MemoryEngine, issue, serve
from leanharbor.pg import PgEngine, lockdown

from leanharbor_calculator import API, KERNEL, STORAGE

# Connections of the PostgreSQL engine's pool.
POOL_SIZE = 16


def required(name: str) -> str:
    value = os.environ.get(name)
    if value is None:
        print(f"{name} is required", file=sys.stderr)
        sys.exit(255)
    return value


def main() -> None:
    secret = required("LEANHARBOR_SECRET").encode()
    who = os.environ.get("LEANHARBOR_ISSUE")
    if who is not None:
        org, _, user = who.partition(":")
        if not (org.isdecimal() and user.isdecimal()):
            print("LEANHARBOR_ISSUE must be <org>:<user>", file=sys.stderr)
            sys.exit(252)
        print(issue(secret, Claims(int(org), int(user), int(time.time()) + 86_400)))
        return
    database = os.environ.get("LEANHARBOR_DATABASE_URL")
    roles = os.environ.get("LEANHARBOR_LOCKDOWN")
    if roles is not None:
        owner, colon, engine_role = roles.partition(":")
        if database is None or not colon:
            print(
                "LEANHARBOR_LOCKDOWN=<owner>:<engine role> needs LEANHARBOR_DATABASE_URL",
                file=sys.stderr,
            )
            sys.exit(252)
        try:
            lockdown(STORAGE, database, owner, engine_role)
        except EngineError as e:
            print(f"lockdown: {e}", file=sys.stderr)
            sys.exit(255)
        return
    engine: Engine
    if database is None:
        engine = MemoryEngine(KERNEL)
    else:
        try:
            engine = PgEngine.connect(STORAGE, database, POOL_SIZE)
        except EngineError as e:
            print(f"LEANHARBOR_DATABASE_URL: {e}", file=sys.stderr)
            sys.exit(255)
    host, _, port = required("LEANHARBOR_LISTEN").rpartition(":")
    serve(engine, API, secret, host, int(port)).serve_forever()


if __name__ == "__main__":
    main()
