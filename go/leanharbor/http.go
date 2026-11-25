package leanharbor

import (
	"encoding/json"
	"errors"
	"io"
	"net/http"
	"strings"
	"time"
)

// Api is how a kernel's commands, replies and refusals appear on the wire, and who a token's
// holder is. Trusted: no theorem covers it.
type Api[Principal, Command, Reply, Error any] interface {
	Principal(tenant, user uint64) Principal
	DecodeCommand(body []byte) (Command, error)
	EncodeReply(reply Reply) any
	EncodeError(refusal Error) (int, any)
	// Fingerprint identifies the command under an idempotency key.
	Fingerprint(cmd Command) []byte
	// Scope separates the idempotency keys of principals of one tenant.
	Scope(actor Principal) string
}

const maxBody = 2 << 20

func reply(w http.ResponseWriter, status int, body any) {
	text, err := json.Marshal(body)
	if err != nil {
		panic(err)
	}
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(status)
	_, _ = w.Write(text)
}

func fail(w http.ResponseWriter, status int, message string) {
	reply(w, status, map[string]string{"error": message})
}

func visible(s string) bool {
	for _, b := range []byte(s) {
		if b != '\t' && (b < 0x20 || b > 0x7e) {
			return false
		}
	}
	return true
}

func header(r *http.Request, name string) (string, bool) {
	values := r.Header[http.CanonicalHeaderKey(name)]
	if len(values) == 0 || !visible(values[0]) {
		return "", false
	}
	return values[0], true
}

func authenticate(verifier *Verifier, r *http.Request) (Claims, error) {
	authorization, ok := header(r, "Authorization")
	if !ok {
		return Claims{}, errors.New("missing authorization header")
	}
	token, ok := strings.CutPrefix(authorization, "Bearer ")
	if !ok {
		return Claims{}, errors.New("authorization is not a bearer token")
	}
	return verifier.Verify(token, uint64(max(time.Now().Unix(), 0)))
}

// RpcHandler serves one kernel command per request, authenticated with secret and run on
// engine. Mount it at `POST /rpc`.
//
// | case | status | body |
// |---|---|---|
// | accepted | 200 | the reply |
// | missing or rejected token | 401 | `{"error": ...}` |
// | body is not a command | 400 | `{"error": ...}` |
// | refused by the kernel | chosen by Api.EncodeError | chosen by Api.EncodeError |
// | idempotency key reused for another command | 422 | `{"error":"idempotency key reused"}` |
// | the engine has stopped | 503 | `{"error":"engine stopped"}` |
func RpcHandler[Principal, Command, Reply, Error any](
	engine Engine[Principal, Command, Reply, Error],
	api Api[Principal, Command, Reply, Error],
	secret []byte,
) http.Handler {
	verifier := NewVerifier(secret)
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		claims, err := authenticate(verifier, r)
		if err != nil {
			fail(w, http.StatusUnauthorized, err.Error())
			return
		}
		actor := api.Principal(claims.Tenant, claims.User)
		body, err := io.ReadAll(http.MaxBytesReader(w, r.Body, maxBody))
		var tooLarge *http.MaxBytesError
		if errors.As(err, &tooLarge) {
			fail(w, http.StatusRequestEntityTooLarge, "request body too large")
			return
		}
		if err != nil {
			fail(w, http.StatusBadRequest, "request body cannot be read")
			return
		}
		if !json.Valid(body) {
			fail(w, http.StatusBadRequest, "body is not JSON")
			return
		}
		cmd, err := api.DecodeCommand(body)
		if err != nil {
			fail(w, http.StatusBadRequest, err.Error())
			return
		}
		var idempotency *Idempotency
		if key, ok := header(r, "Idempotency-Key"); ok {
			idempotency = &Idempotency{
				Scope:       api.Scope(actor),
				Key:         key,
				Fingerprint: api.Fingerprint(cmd),
			}
		}
		result, refusal, err := engine.Execute(actor, cmd, idempotency)
		switch {
		case errors.Is(err, ErrIdempotencyConflict):
			fail(w, http.StatusUnprocessableEntity, "idempotency key reused")
		case err != nil:
			fail(w, http.StatusServiceUnavailable, "engine stopped")
		case refusal != nil:
			status, body := api.EncodeError(*refusal)
			reply(w, status, body)
		default:
			reply(w, http.StatusOK, api.EncodeReply(result))
		}
	})
}
