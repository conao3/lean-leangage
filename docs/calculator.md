# The calculator

[`lean/Calculator/Kernel.lean`](../lean/Calculator/Kernel.lean) keeps one number per user:

```lean
def transition (actor : Principal) (snap : Snapshot) (cmd : Command) :
    Except Error (Option Memory × Reply) :=
  match cmd with
  | .set value => .ok (some { user := actor.user, value }, .value value)
  | .apply op arg =>
    match compute op (memoryOf snap.memories actor.user) arg with
    | .ok v => .ok (some { user := actor.user, value := v }, .value v)
    | .error e => .error e
  | .get => .ok (none, .value (memoryOf snap.memories actor.user))
```

A tenant's numbers are a binary trie on the user id, lowest bit first. A command visits at most
64 nodes, and about log₂ n in a tenant whose n user ids are 0 to n − 1. `memoryOf` reads a number and `apply` stores one with `store`.

Among the theorems of [`lean/Calculator/Proofs.lean`](../lean/Calculator/Proofs.lean):

| Theorem | Statement |
|---|---|
| `transition_spec` | the reply is `specStep` (arithmetic on unbounded naturals) of the caller's number, and the command is refused exactly when `specStep` refuses |
| `compute_spec` | `compute` is `+`, `-`, `*`, `/` on naturals when the result fits 64 bits, and a refusal otherwise |
| `get_after` | after an accepted command, `get` by the same user returns that command's reply |
| `others_unchanged` | a command leaves every other user's number as it was |
| `read_only_sound` | `get` returns no writes (the obligation `ReadOnlySound`) |
| `memoryOf_store` | after `store k v`, `memoryOf` returns `v` for `k` and what it returned before for every other id |

[`lean/Calculator/Wire.lean`](../lean/Calculator/Wire.lean) is what a server does with a request
around that kernel, and [`lean/Leangage/Http.lean`](../lean/Leangage/Http.lean) the part of it
that is the same for every kernel. A handler reads the JSON text of the body with the JSON library
of its language and passes the header and the tokens of the body through 3 generated functions:

1. `authenticate` reads the `Authorization` header into the claims of its token, the bytes the
   tag signs and the tag, or gives the answer (401). The handler computes the HMAC-SHA256 of those
   bytes and compares it with the tag.
2. `request` takes the claims, the time and the body: the tokens the JSON library read, in the
   order of the text, or the fact that it read none
   ([`lean/Leangage/Json/Lexemes.lean`](../lean/Leangage/Json/Lexemes.lean)). The tokens come packed
   in one text: a character for the kind of each token, a line feed, and the texts of the
   numbers, the strings and the keys, each but the last after the count of its characters and a
   colon. It refuses an expired
   token, decides from the tokens (member names and strings compared as text; `numberOf`
   decides which number tokens are a number below 2^64 in decimal digits) and gives the command
   and the principal the engine runs, or the answer (401, 400, 413).
3. `respond` gives the status and the body for the kernel's reply or refusal, and `failed` for a
   failure of the engine.

[`lean/Calculator/Wire/Proofs.lean`](../lean/Calculator/Wire/Proofs.lean),
[`lean/Leangage/Http/Proofs.lean`](../lean/Leangage/Http/Proofs.lean) and
[`lean/Leangage/Json/Lexemes/Proofs.lean`](../lean/Leangage/Json/Lexemes/Proofs.lean) prove:

| Theorem | Statement |
|---|---|
| `numberOf_iff` | a number token is the number `n` below 2^64 exactly when its text is the decimal of `n`: digits without a sign, a fraction, an exponent or a leading zero |
| `decode_encode` | every command has a JSON spelling (`{"cmd":"set","value":6}`, `{"cmd":"apply","op":"mul","arg":7}`, `{"cmd":"get"}`) whose tokens decode to it |
| `decode_ok_iff`, `object_iff` | tokens decode to a command exactly when they are those of an object with the fields of that command, in any order and with no other member |
| `decode_eq` | `decode`, which reads a command whose members come in the order above from the start of the packed text and the number at its end (`spelled`), decides as the lookup of the members by their names (`decodeObject`) on the tokens the text unpacks to, for every body, and answers a text that no list of tokens packs to as no JSON |
| `unpack_pack`, `unpack_iff` | `unpack` gives back, one by one, the tokens that a conversion packs into one text (`pack`), and gives tokens for no other text |
| `authenticate_ok_iff`, `authenticate_sound` | the headers accepted are `Bearer <t>` with a token `t` that `parseString` accepts, and the bytes returned for the HMAC are every byte of `t` before its last dot |
| `authenticate_missing`, `authenticate_not_bearer`, `authenticate_bearer` | a request without the header, with another scheme or with a malformed token is answered 401 with its message |
| `request_expired`, `request_json`, `request_not_json` | an expired token is answered 401 whatever the body; a body that is not a command is answered 400 with the message of its refusal, and so is a body the JSON library refuses |
| `respond_ok`, `respond_error`, `failed_spec` | an accepted command is answered 200 with `{"value": v}`, a refused one 422 with `{"error": name}`, and each failure of the engine with its status and `{"error": message}` |
| `fingerprint_injective`, `scope_injective` | different commands have different fingerprints under an idempotency key, and the keys of different users are kept apart |

The Rust server is the generated kernel and those functions behind an ordinary axum router
([`rust/calculator`](../rust/calculator)):

```console
$ export LEANGAGE_SECRET=dev-secret
$ TOKEN=$(cd rust && LEANGAGE_ISSUE=1:7 cargo run --release -q --bin leangage-calculator)
$ cd rust && LEANGAGE_LISTEN=127.0.0.1:8080 cargo run --release -q --bin leangage-calculator &
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"set","value":6}' 127.0.0.1:8080/rpc
{"value":6}
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"apply","op":"mul","arg":7}' 127.0.0.1:8080/rpc
{"value":42}
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"get"}' 127.0.0.1:8080/rpc
{"value":42}
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"apply","op":"div","arg":0}' 127.0.0.1:8080/rpc
{"error":"division_by_zero"}
```

The Python server ([`python/src/leangage_calculator`](../python/src/leangage_calculator)) runs
the same Lean modules, generated to Python, and the Go server
([`go/calculator`](../go/calculator)) runs them generated to Go. A command, a body that is not one
and a token that is refused get the same status and body from the 3 servers, and a token issued
by one is accepted by the others:

```console
$ cd python && LEANGAGE_LISTEN=127.0.0.1:8081 uv run leangage-calculator &
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"set","value":6}' 127.0.0.1:8081/rpc
{"value":6}
$ cd go && LEANGAGE_LISTEN=127.0.0.1:8082 go run ./calculator/cmd/leangage-calculator &
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"set","value":6}' 127.0.0.1:8082/rpc
{"value":6}
```
