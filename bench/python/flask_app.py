"""Flask with no kernel: decodes the JSON body and replies with a JSON value."""

from flask import Flask, jsonify, request

app = Flask(__name__)


@app.post("/rpc")
def rpc():
    request.get_json(force=True)
    return jsonify(value=6)
