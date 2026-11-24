"""FastAPI with no kernel: decodes the JSON body and replies with a JSON value."""

from typing import Any

from fastapi import FastAPI

app = FastAPI()


@app.post("/rpc")
async def rpc(body: dict[str, Any]) -> dict[str, int]:
    return {"value": 6}
