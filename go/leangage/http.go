package leangage

import (
	"errors"
	"io"
	"net/http"
	"time"

	"github.com/conao3/lean-leangage/go/leangage/httpformat"
)

// Api is a kernel's functions on the wire, implemented by delegating to functions generated
// from Lean.
type Api[Principal, Command, Reply, Error any] interface {
	// Request is what the engine runs for a request whose token, checked, claims tenant, user
	// and expiry, at the time now; or the answer to the request.
	Request(tenant, user, expiry, now uint64, body httpformat.Body) (Principal, Command, *httpformat.Response)
	// Respond is the answer to a command the kernel accepted (refusal is nil) or refused.
	Respond(reply Reply, refusal *Error) httpformat.Response
	// Fingerprint identifies the command under an idempotency key.
	Fingerprint(cmd Command) []byte
	// Scope separates the idempotency keys of principals of one tenant.
	Scope(actor Principal) string
}

const maxBody = 2 << 20

// send writes a generated answer.
func send(w http.ResponseWriter, answer httpformat.Response) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(int(answer.Status))
	_, _ = w.Write(answer.Body)
}

func visible(s string) bool {
	for _, b := range []byte(s) {
		if b != '\t' && (b < 0x20 || b > 0x7e) {
			return false
		}
	}
	return true
}

func header(r *http.Request, name string) *string {
	values := r.Header[http.CanonicalHeaderKey(name)]
	if len(values) == 0 || !visible(values[0]) {
		return nil
	}
	return &values[0]
}

// bodyOf reads the body as the generated functions take it.
func bodyOf(w http.ResponseWriter, r *http.Request) httpformat.Body {
	body, err := io.ReadAll(http.MaxBytesReader(w, r.Body, maxBody))
	var tooLarge *http.MaxBytesError
	switch {
	case errors.As(err, &tooLarge):
		return httpformat.BodyTooLarge{}
	case err != nil:
		return httpformat.BodyUnreadable{}
	}
	return BodyOf(body)
}

// BodyOf is the bytes of a body as the generated functions take them: its tokens, or that it is
// not a JSON text.
func BodyOf(body []byte) httpformat.Body {
	tokens, ok := Tokens(body)
	if !ok {
		return httpformat.BodyNotJson{}
	}
	return httpformat.BodyJson{Tokens: tokens}
}

// failure is the failure a generated answer is made of.
func failure(err error) httpformat.Failure {
	switch {
	case errors.Is(err, ErrIdempotencyConflict):
		return httpformat.FailureConflict()
	case errors.Is(err, ErrStopped):
		return httpformat.FailureStopped()
	case errors.Is(err, ErrRetriesExhausted):
		return httpformat.FailureRetriesExhausted()
	case errors.Is(err, ErrDatabase):
		return httpformat.FailureDatabase()
	case errors.Is(err, ErrCommitUnknown):
		return httpformat.FailureCommitUnknown()
	}
	return httpformat.FailureBroken()
}

// RpcHandler serves one kernel command per request, authenticated with secret and run on
// engine. Mount it at `POST /rpc`.
//
// The handler passes the request to generated functions and sends what they return. It gives
// the `Authorization` header to Verifier.Admit, which calls httpformat.Authenticate and checks
// the tag; it gives the claims, the time and the body to Api.Request; it runs the command on
// the engine; and it gives the kernel's decision to Api.Respond and a failure of the engine to
// httpformat.Failed. The status and the body of every answer come from those functions, which
// are generated from `lean/Leangage/Http.lean` and from the kernel's module beside it
// (`lean/Calculator/Wire.lean`).
func RpcHandler[Principal, Command, Reply, Error any](
	engine Engine[Principal, Command, Reply, Error],
	api Api[Principal, Command, Reply, Error],
	secret []byte,
) http.Handler {
	verifier := NewVerifier(secret)
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		claims, answer := verifier.Admit(header(r, "Authorization"))
		if answer != nil {
			send(w, *answer)
			return
		}
		now := uint64(max(time.Now().Unix(), 0))
		actor, cmd, answer := api.Request(claims.Tenant, claims.User, claims.Expiry, now, bodyOf(w, r))
		if answer != nil {
			send(w, *answer)
			return
		}
		var idempotency *Idempotency
		if key := header(r, "Idempotency-Key"); key != nil {
			idempotency = &Idempotency{
				Scope:       api.Scope(actor),
				Key:         *key,
				Fingerprint: api.Fingerprint(cmd),
			}
		}
		reply, refusal, err := engine.Execute(actor, cmd, idempotency)
		if err != nil {
			send(w, httpformat.Failed(failure(err)))
			return
		}
		send(w, api.Respond(reply, refusal))
	})
}
