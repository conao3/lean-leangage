// net/http with no kernel: decodes the JSON body and replies with a JSON value.
package main

import (
	"encoding/json"
	"log"
	"net/http"
	"os"
)

func main() {
	http.HandleFunc("POST /rpc", func(w http.ResponseWriter, r *http.Request) {
		var body map[string]any
		if err := json.NewDecoder(r.Body).Decode(&body); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]uint64{"value": 6})
	})
	log.Fatal(http.ListenAndServe(os.Getenv("BENCH_LISTEN"), nil))
}
