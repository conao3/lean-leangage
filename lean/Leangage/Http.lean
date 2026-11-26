import Leangage.Token
import Leangage.Json
import Leangage.Json.Items

/-!
# Requests and responses

What a server decides about a request apart from the kernel's command: who the bearer token of
the `Authorization` header claims to be, whether the token has expired, what a body that is not a
JSON text is answered with, and the status and the body of each answer that is not the
kernel's. A server calls `authenticate` with the header, checks the HMAC tag of the result
itself, and answers a failure of its own with `failed`. A kernel's `request` starts with
`admit`.
-/

namespace Leangage.Http

/-- The status code and the bytes of the body of an answer. -/
structure Response where
  status : UInt16
  body : Array UInt8
deriving DecidableEq, Repr

/-- The body of a request as the server read it. -/
inductive Body where
  /-- The tokens of the JSON text of the body, in the order of the document. -/
  | json (lexemes : List Json.Items.Lexeme)
  /-- The JSON library refused the bytes. -/
  | notJson
  /-- The body is longer than the server reads. -/
  | tooLarge
  /-- The connection failed while the server read the body. -/
  | unreadable
deriving DecidableEq, Repr

/-- Why the server answers without the kernel's decision. -/
inductive Failure where
  /-- The HMAC tag of the token is not the tag of its payload. -/
  | badSignature
  /-- The idempotency key was used before with another command. -/
  | conflict
  | stopped
  | retriesExhausted
  | database
  | commitUnknown
  | broken
deriving DecidableEq, Repr

/-- What a bearer token claims, the bytes its tag signs and the tag. -/
structure Bearer where
  tenant : UInt64
  user : UInt64
  exp : UInt64
  payload : Array UInt8
  sig : Array UInt8
deriving DecidableEq, Repr

/-- `{"error":"<message>"}` with a status. -/
def refuse (status : UInt16) (message : String) : Response :=
  ⟨status, Json.writeArray [.objOpen, .key "error", .str message, .objClose]⟩

/-- The token of `Bearer <token>`. -/
def bearerToken (header : String) : Option String :=
  (header.dropPrefix? "Bearer ").map (·.copy)

/-- The claims of the token in the `Authorization` header, or the answer to a request without
one. The server then checks the tag. -/
def authenticate (header : Option String) : Except Response Bearer :=
  match header with
  | none => .error (refuse 401 "missing authorization header")
  | some h =>
    match bearerToken h with
    | none => .error (refuse 401 "authorization is not a bearer token")
    | some tok =>
      match Token.parseString tok with
      | none => .error (refuse 401 "malformed token")
      | some p => .ok ⟨p.tenant, p.user, p.exp, p.payload, p.sig⟩

/-- The items of the body of a request whose token expires at `exp`, at the time `now`. -/
def admit (exp now : UInt64) (body : Body) : Except Response (List Json.Items.Item) :=
  if exp < now then .error (refuse 401 "token expired")
  else
    match body with
    | .json lexemes => .ok (Json.Items.items lexemes)
    | .notJson => .error (refuse 400 "body is not JSON")
    | .tooLarge => .error (refuse 413 "request body too large")
    | .unreadable => .error (refuse 400 "request body cannot be read")

def failed : Failure → Response
  | .badSignature => refuse 401 "bad token signature"
  | .conflict => refuse 422 "idempotency key reused"
  | .stopped => refuse 503 "engine stopped"
  | .retriesExhausted => refuse 503 "retries exhausted"
  | .database => refuse 503 "database error"
  | .commitUnknown => refuse 500 "commit outcome unknown"
  | .broken => refuse 500 "engine error"

end Leangage.Http
