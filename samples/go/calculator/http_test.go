package calculator

import (
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/conao3/lean-leangage/langs/go/leangage"
)

// Requests to `POST /rpc` get the statuses and bodies of the Rust server.
func TestRpc(t *testing.T) {
	secret := []byte("secret")
	engine := NewEngine()
	defer engine.Close()
	handler := leangage.RpcHandler(engine, Calculator{}, secret)
	bearer := func(user uint64) string {
		return "Bearer " + leangage.Issue(secret, leangage.Claims{Tenant: 1, User: user, Expiry: 1 << 62})
	}
	steps := []struct {
		user   uint64
		key    string
		body   string
		status int
		want   string
	}{
		{7, "", `{"cmd":"set","value":6}`, 200, `{"value":6}`},
		{7, "", `{"cmd":"apply","op":"mul","arg":7}`, 200, `{"value":42}`},
		{7, "", `{"cmd":"get"}`, 200, `{"value":42}`},
		{7, "", `{"cmd":"apply","op":"div","arg":0}`, 422, `{"error":"division_by_zero"}`},
		{7, "", `{"cmd":"apply","op":"sub","arg":43}`, 422, `{"error":"underflow"}`},
		{7, "", `{"cmd":"apply","op":"add","arg":18446744073709551615}`, 422, `{"error":"overflow"}`},
		{8, "", ` { "value" : 18446744073709551615 , "cmd" : "set" } `, 200, `{"value":18446744073709551615}`},
		{8, "", `{"cmd":"get"}`, 200, `{"value":18446744073709551615}`},
		{7, "", `{"cmd":"get"}`, 200, `{"value":42}`},
		{7, "k", `{"cmd":"apply","op":"add","arg":1}`, 200, `{"value":43}`},
		{7, "k", `{"cmd":"apply","op":"add","arg":1}`, 200, `{"value":43}`},
		{7, "k", `{"cmd":"apply","op":"add","arg":2}`, 422, `{"error":"idempotency key reused"}`},
		{8, "k", `{"cmd":"set","value":1}`, 200, `{"value":1}`},
		{7, "r", `{"cmd":"apply","op":"div","arg":0}`, 422, `{"error":"division_by_zero"}`},
		{7, "r", `{"cmd":"apply","op":"div","arg":43}`, 200, `{"value":1}`},
		{7, "", `{"cmd":"set"}`, 400, `{"error":"not a calculator command"}`},
		{7, "", `{"cmd":"set","value":6,"arg":1}`, 400, `{"error":"not a calculator command"}`},
		{7, "", `{"cmd":"get","value":6}`, 400, `{"error":"not a calculator command"}`},
		{7, "", `{"cmd":"apply","op":"pow","arg":1}`, 400, `{"error":"not a calculator command"}`},
		{7, "", `{"cmd":"apply","op":null,"arg":1}`, 400, `{"error":"not a calculator command"}`},
		{7, "", `{"CMD":"get"}`, 400, "{\"error\":\"missing field `cmd`\"}"},
		{7, "", `{"cmd":"set","Value":6}`, 400, `{"error":"not a calculator command"}`},
		{7, "", `{"cmd":"set","value":"6"}`, 400, "{\"error\":\"`value` must be an integer below 2^64\"}"},
		{7, "", `{"cmd":"set","value":6.0}`, 400, "{\"error\":\"`value` must be an integer below 2^64\"}"},
		{7, "", `{"cmd":"set","value":-1}`, 400, "{\"error\":\"`value` must be an integer below 2^64\"}"},
		{7, "", `{"cmd":"set","value":null}`, 400, "{\"error\":\"`value` must be an integer below 2^64\"}"},
		{7, "", `{"cmd":"set","value":18446744073709551616}`, 400, "{\"error\":\"`value` must be an integer below 2^64\"}"},
		{7, "", `[]`, 400, `{"error":"not a calculator command"}`},
		{7, "", `null`, 400, `{"error":"not a calculator command"}`},
		{7, "", `{"cmd":"get"} x`, 400, `{"error":"body is not JSON"}`},
		{7, "", `{"cmd":"get","cmd":"get"}`, 400, `{"error":"not a calculator command"}`},
		{7, "", `{"cmd":"apply","op":"add","arg":1.5}`, 400, "{\"error\":\"`arg` must be an integer below 2^64\"}"},
		{7, "", "\xff", 400, `{"error":"body is not JSON"}`},
		{7, "", strings.Repeat("[", 2<<20), 400, `{"error":"body is not JSON"}`},
		{7, "", strings.Repeat("[", 10_000) + strings.Repeat("]", 10_000), 400, `{"error":"not a calculator command"}`},
		{7, "", strings.Repeat("[", 10_001) + strings.Repeat("]", 10_001), 400, `{"error":"body is not JSON"}`},
		{7, "", strings.Repeat("[", 2<<20+1), 413, `{"error":"request body too large"}`},
		{7, "", `{"cmd":"get"}`, 200, `{"value":1}`},
	}
	for i, step := range steps {
		request := httptest.NewRequest(http.MethodPost, "/rpc", strings.NewReader(step.body))
		request.Header.Set("Authorization", bearer(step.user))
		if step.key != "" {
			request.Header.Set("Idempotency-Key", step.key)
		}
		response := httptest.NewRecorder()
		handler.ServeHTTP(response, request)
		if response.Code != step.status || response.Body.String() != step.want {
			t.Fatalf("step %d: %.60s: got %d %s", i, step.body, response.Code, response.Body.String())
		}
		if got := response.Header().Get("Content-Type"); got != "application/json" {
			t.Fatalf("step %d: content type %q", i, got)
		}
	}
}
