import Leangage.Http
import Leangage.Token.Proofs
import Leangage.Json.Proofs

/-!
# What the functions on requests and responses guarantee

- `refuse_status`, `refuse_body`: `refuse status message` has that status, and its body is
  `Value.print` of `{"error": message}`.
- `authenticate_missing`, `authenticate_not_bearer` (`authenticate_other`), `authenticate_bearer`: a request without the
  header is answered 401 `missing authorization header`; a header that is not `Bearer ` followed
  by a text is answered 401 `authorization is not a bearer token`; the header `Bearer <t>` is
  answered 401 `malformed token` when `Token.parseString t` refuses `t`, and gives the fields
  `parseString` returns otherwise.
- `authenticate_ok_iff`: `authenticate` accepts exactly the headers `Bearer <t>` whose `t`
  `parseString` accepts. `authenticate_sound`: for an accepted header, the bytes of `t` are
  `Token.join` of the payload and the tag returned, and the payload is `Token.encodePayload` of
  the tenant, the user and the expiry returned. So the bytes a server checks the tag over are
  every byte of the token before its last dot, and they fix the claims.
  `authenticate_issued`: the header of an issued token gives back what was signed.
- `admit_expired`, `admit_text`, `admit_not_text`: a token whose expiry is before `now` is
  answered 401 `token expired`, whatever the body; otherwise a body that is text is passed on, and
  one that is not is answered 400 `body is not JSON`, 413 `request body too large` or 400
  `request body cannot be read`.
- `failed_spec`: the status and the message of each failure.
-/

namespace Leangage.Http

open Leangage.Token (bytesOf)
open Leangage.Json (Value)

/-- `{"error": message}`. -/
def errorValue (message : String) : Value :=
  .obj [(Json.ascii ['e', 'r', 'r', 'o', 'r'], .str (bytesOf message))]

theorem refuse_status (status : UInt16) (message : String) : (refuse status message).status = status :=
  rfl

/-- The body of a refusal is the JSON value `{"error": message}`. -/
theorem refuse_body (status : UInt16) (message : String) :
    (refuse status message).body.toList = (errorValue message).print := by
  apply Json.writeArray_value
  simp only [List.map, Json.StrTok.toTok, errorValue, Value.toks, Json.membersToks]
  congr

theorem bearerToken_some {h t : String} (hb : bearerToken h = some t) : h = "Bearer " ++ t := by
  simp only [bearerToken, Option.map_eq_some_iff] at hb
  obtain ⟨res, hres, rfl⟩ := hb
  exact String.eq_append_of_dropPrefix?_string_eq_some hres

theorem bearerToken_append (t : String) : bearerToken ("Bearer " ++ t) = some t := by
  cases hb : bearerToken ("Bearer " ++ t) with
  | some t' => rw [(String.append_right_inj _).mp (bearerToken_some hb)]
  | none =>
    exfalso
    simp only [bearerToken, Option.map_eq_none_iff] at hb
    rw [String.dropPrefix?_eq_dropPrefix?_toSlice, String.Slice.dropPrefix?_eq_none_iff] at hb
    simp at hb

theorem bearerToken_eq_some_iff {h t : String} : bearerToken h = some t ↔ h = "Bearer " ++ t :=
  ⟨bearerToken_some, fun e => e ▸ bearerToken_append t⟩

theorem bearerToken_none {h : String} (hn : ∀ t, h ≠ "Bearer " ++ t) : bearerToken h = none := by
  cases hb : bearerToken h with
  | none => rfl
  | some t => exact absurd (bearerToken_some hb) (hn t)

/-- A request without the header. -/
theorem authenticate_missing :
    authenticate none = .error (refuse 401 "missing authorization header") :=
  rfl

/-- A header that is not `Bearer ` and a text. -/
theorem authenticate_not_bearer {h : String} (hn : ∀ t, h ≠ "Bearer " ++ t) :
    authenticate (some h) = .error (refuse 401 "authorization is not a bearer token") := by
  simp [authenticate, bearerToken_none hn]

/-- A header that does not start with `Bearer `. -/
theorem authenticate_other (h : String) (hn : h.startsWith "Bearer " = false) :
    authenticate (some h) = .error (refuse 401 "authorization is not a bearer token") := by
  apply authenticate_not_bearer
  intro t e
  subst e
  simp at hn

/-- The header `Bearer <t>` is decided by `Token.parseString t`. -/
theorem authenticate_bearer (t : String) :
    authenticate (some ("Bearer " ++ t)) =
      match Token.parseString t with
      | none => .error (refuse 401 "malformed token")
      | some p => .ok ⟨p.tenant, p.user, p.exp, p.payload, p.sig⟩ := by
  simp only [authenticate, bearerToken_append]
  cases Token.parseString t <;> rfl

/-- `authenticate` accepts exactly the headers `Bearer <t>` whose `t` `parseString` accepts. -/
theorem authenticate_ok_iff {header : Option String} {b : Bearer} :
    authenticate header = .ok b ↔
      ∃ t p, header = some ("Bearer " ++ t) ∧ Token.parseString t = some p ∧
        b = ⟨p.tenant, p.user, p.exp, p.payload, p.sig⟩ := by
  constructor
  · intro h
    cases header with
    | none => cases h
    | some hd =>
      cases hb : bearerToken hd with
      | none => simp [authenticate, hb] at h
      | some t =>
        have he := bearerToken_some hb
        subst he
        rw [authenticate_bearer] at h
        cases hp : Token.parseString t with
        | none => simp [hp] at h
        | some p =>
          simp only [hp, Except.ok.injEq] at h
          exact ⟨t, p, rfl, hp, h.symm⟩
  · rintro ⟨t, p, rfl, hp, rfl⟩
    rw [authenticate_bearer, hp]

/-- What a server checks the tag over: for an accepted header `Bearer <t>`, `t` is `join` of the
payload and the tag returned, and the payload is `encodePayload` of the claims returned. -/
theorem authenticate_sound {header : Option String} {b : Bearer} (h : authenticate header = .ok b) :
    ∃ t, header = some ("Bearer " ++ t) ∧
      bytesOf t = Token.join b.payload.toList b.sig.toList ∧
      b.payload.toList = Token.encodePayload b.tenant b.user b.exp := by
  obtain ⟨t, p, rfl, hp, rfl⟩ := authenticate_ok_iff.mp h
  have hc := Token.parseString_canon hp
  exact ⟨t, rfl, hc.2, hc.1⟩

/-- The header of an issued token gives back what was signed. -/
theorem authenticate_issued {t : String} (tenant user exp : UInt64) (sig : List UInt8)
    (h : bytesOf t = Token.join (Token.encodePayload tenant user exp) sig) :
    authenticate (some ("Bearer " ++ t)) =
      .ok ⟨tenant, user, exp, (Token.encodePayload tenant user exp).toArray, sig.toArray⟩ := by
  rw [authenticate_bearer, Token.parseString_join tenant user exp sig h]

/-- An expired token is refused, whatever the body. -/
theorem admit_expired {exp now : UInt64} (h : exp < now) (body : Body) :
    admit exp now body = .error (refuse 401 "token expired") := by
  simp [admit, h]

/-- The text of a body passes with a token that has not expired. -/
theorem admit_text {exp now : UInt64} (h : ¬exp < now) (s : String) :
    admit exp now (.text s) = .ok s := by
  simp [admit, h]

/-- A body that is not text, with a token that has not expired. -/
theorem admit_not_text {exp now : UInt64} (h : ¬exp < now) :
    admit exp now .notUtf8 = .error (refuse 400 "body is not JSON") ∧
      admit exp now .tooLarge = .error (refuse 413 "request body too large") ∧
      admit exp now .unreadable = .error (refuse 400 "request body cannot be read") := by
  simp [admit, h]

/-- The status of a failure. -/
def failureStatus : Failure → UInt16
  | .badSignature => 401
  | .conflict => 422
  | .stopped | .retriesExhausted | .database => 503
  | .commitUnknown | .broken => 500

/-- The message of a failure. -/
def failureMessage : Failure → List Char
  | .badSignature => "bad token signature".toList
  | .conflict => "idempotency key reused".toList
  | .stopped => "engine stopped".toList
  | .retriesExhausted => "retries exhausted".toList
  | .database => "database error".toList
  | .commitUnknown => "commit outcome unknown".toList
  | .broken => "engine error".toList

/-- The status and the body of each failure. -/
theorem failed_spec (f : Failure) :
    (failed f).status = failureStatus f ∧
      (failed f).body.toList =
        (Value.obj [(Json.ascii ['e', 'r', 'r', 'o', 'r'], .str (Json.ascii (failureMessage f)))]).print := by
  cases f <;> exact ⟨rfl, by rw [failed, refuse_body]; rfl⟩

end Leangage.Http
