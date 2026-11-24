import os
import sys
import time

from leanharbor import Claims, MemoryEngine, issue, serve

from leanharbor_calculator import API, KERNEL


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
    host, _, port = required("LEANHARBOR_LISTEN").rpartition(":")
    serve(MemoryEngine(KERNEL), API, secret, host, int(port)).serve_forever()


if __name__ == "__main__":
    main()
