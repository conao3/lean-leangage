package leangage

import (
	"errors"
	"net/http"
	"net/http/httptest"
	"strconv"
	"strings"
	"testing"

	"github.com/conao3/leanfran-go"

	"github.com/conao3/lean-leangage/go/leangage/gen/httpformat"
	"github.com/conao3/lean-leangage/go/leangage/gen/jsonlexemes"
)

// counterApi reads a body that is one number in decimal, written by hand.
type counterApi struct{}

func (counterApi) Request(tenant, user, expiry, now uint64, body httpformat.Body) (who, int, *httpformat.Response) {
	_, err := httpformat.Admit(expiry, now, body)
	if answer, ok := errors.AsType[*leanfran.ExceptError[httpformat.Response]](err); ok {
		return who{}, 0, &answer.Value
	}
	if read, ok := body.(httpformat.BodyJson); ok {
		if lexemes, _ := unpacked(read.Packed); len(lexemes) == 1 {
			if number, ok := lexemes[0].(jsonlexemes.LexemeNumber); ok {
				if cmd, err := strconv.Atoi(number.Text); err == nil {
					return who{tenant, user}, cmd, nil
				}
			}
		}
	}
	answer, _ := httpformat.Refuse(400, "not a number")
	return who{}, 0, &answer
}

func (counterApi) Respond(reply int, refusal *string) httpformat.Response {
	if refusal != nil {
		answer, _ := httpformat.Refuse(409, *refusal)
		return answer
	}
	return httpformat.Response{Status: 200, Body: []byte(strconv.Itoa(reply))}
}

func (counterApi) Fingerprint(cmd int) []byte { return []byte(strconv.Itoa(cmd)) }

func (counterApi) Scope(actor who) string { return strconv.FormatUint(actor.user, 10) }

func TestRpcStatuses(t *testing.T) {
	secret := []byte("secret")
	handler := RpcHandler(NewMemoryEngine(counter{}), counterApi{}, secret)
	token := Issue(secret, Claims{Tenant: 1, User: 1, Expiry: 1 << 62})
	post := func(authorization, key, body string) (int, string) {
		request := httptest.NewRequest(http.MethodPost, "/rpc", strings.NewReader(body))
		if authorization != "" {
			request.Header.Set("Authorization", authorization)
		}
		if key != "" {
			request.Header.Set("Idempotency-Key", key)
		}
		response := httptest.NewRecorder()
		func() {
			defer func() {
				if recover() != nil {
					response.Code = 0
				}
			}()
			handler.ServeHTTP(response, request)
		}()
		if response.Code != 0 && response.Header().Get("Content-Type") != "application/json" {
			t.Errorf("content type %q", response.Header().Get("Content-Type"))
		}
		return response.Code, response.Body.String()
	}
	steps := []struct {
		authorization, key, body string
		status                   int
		want                     string
	}{
		{"", "", "1", 401, `{"error":"missing authorization header"}`},
		{"Basic " + token, "", "1", 401, `{"error":"authorization is not a bearer token"}`},
		{"Bearer v1.1.1", "", "1", 401, `{"error":"malformed token"}`},
		{"Bearer " + Issue([]byte("other"), Claims{Tenant: 1, User: 1, Expiry: 1 << 62}), "", "1", 401, `{"error":"bad token signature"}`},
		{"Bearer " + Issue([]byte("other"), Claims{Tenant: 1, User: 1, Expiry: 1}), "", "1", 401, `{"error":"bad token signature"}`},
		{"Bearer " + Issue(secret, Claims{Tenant: 1, User: 1, Expiry: 1}), "", "1", 401, `{"error":"token expired"}`},
		{"Bearer " + Issue(secret, Claims{Tenant: 1, User: 1, Expiry: 1}), "", "\xff", 401, `{"error":"token expired"}`},
		{"Bearer " + token, "", "\xff", 400, `{"error":"body is not JSON"}`},
		{"Bearer " + token, "", strings.Repeat("1", 2<<20+1), 413, `{"error":"request body too large"}`},
		{"Bearer " + token, "", `"one"`, 400, `{"error":"not a number"}`},
		{"Bearer " + token, "", "5", 200, "5"},
		{"Bearer " + token, "a", "2", 200, "7"},
		{"Bearer " + token, "a", "2", 200, "7"},
		{"Bearer " + token, "a", "3", 422, `{"error":"idempotency key reused"}`},
		{"Bearer " + token, "b", "-1", 409, `{"error":"negative"}`},
		{"Bearer " + token, "b", "1", 200, "8"},
		{"Bearer " + token, "", "0", 0, ""},
		{"Bearer " + token, "", "1", 503, `{"error":"engine stopped"}`},
	}
	for i, step := range steps {
		status, body := post(step.authorization, step.key, step.body)
		if status != step.status || body != step.want {
			t.Fatalf("step %d: got %d %s", i, status, body)
		}
	}
}
