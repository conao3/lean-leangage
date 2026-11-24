// Command leanharbor-calculator serves the calculator, or with LEANHARBOR_ISSUE prints a
// one-day token and exits.
package main

import (
	"fmt"
	"net/http"
	"os"
	"strconv"
	"strings"
	"time"

	"github.com/conao3/lean-leanharbor/go/calculator"
	"github.com/conao3/lean-leanharbor/go/leanharbor"
)

func required(name string) string {
	value, ok := os.LookupEnv(name)
	if !ok {
		fmt.Fprintf(os.Stderr, "%s is required\n", name)
		os.Exit(255)
	}
	return value
}

func main() {
	secret := []byte(required("LEANHARBOR_SECRET"))
	if who, ok := os.LookupEnv("LEANHARBOR_ISSUE"); ok {
		org, user, _ := strings.Cut(who, ":")
		tenant, errTenant := strconv.ParseUint(org, 10, 64)
		id, errUser := strconv.ParseUint(user, 10, 64)
		if errTenant != nil || errUser != nil {
			fmt.Fprintln(os.Stderr, "LEANHARBOR_ISSUE must be <org>:<user>")
			os.Exit(252)
		}
		expiry := uint64(time.Now().Unix()) + 86_400
		fmt.Println(leanharbor.Issue(secret, leanharbor.Claims{Tenant: tenant, User: id, Expiry: expiry}))
		return
	}
	mux := http.NewServeMux()
	mux.HandleFunc("GET /healthz", func(w http.ResponseWriter, _ *http.Request) {
		_, _ = w.Write([]byte("ok"))
	})
	mux.Handle("POST /rpc", leanharbor.RpcHandler(calculator.NewEngine(), calculator.Calculator{}, secret))
	if err := http.ListenAndServe(required("LEANHARBOR_LISTEN"), mux); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
