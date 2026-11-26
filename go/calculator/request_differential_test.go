package calculator

import (
	"bytes"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"regexp"
	"strconv"
	"strings"
	"testing"
	"unicode/utf8"

	"github.com/conao3/leanfran-go"

	"github.com/conao3/lean-leangage/go/calculator/kernel"
	"github.com/conao3/lean-leangage/go/calculator/wire"
	"github.com/conao3/lean-leangage/go/leangage/httpformat"
	"github.com/conao3/lean-leangage/go/leangage/jsonread"
)

const requestCases = "../../testdata/request-cases.txt"

var surrogateEscape = regexp.MustCompile(`\\u[dD][89a-fA-F]`)

func requestBytes(t *testing.T, word string) []byte {
	t.Helper()
	out, err := hex.DecodeString(strings.TrimPrefix(word, "x"))
	if err != nil || !strings.HasPrefix(word, "x") {
		t.Fatalf("bad bytes %s", word)
	}
	return out
}

func showRequestBytes(b []byte) string { return "x" + hex.EncodeToString(b) }

func requestNumber(t *testing.T, word string) uint64 {
	t.Helper()
	n, err := strconv.ParseUint(word, 10, 64)
	if err != nil {
		t.Fatalf("bad number %s", word)
	}
	return n
}

func showItem(item jsonread.Item) string {
	switch item := item.(type) {
	case jsonread.ItemNull:
		return "n"
	case jsonread.ItemBool:
		if item.B {
			return "t"
		}
		return "f"
	case jsonread.ItemNum:
		return "u" + strconv.FormatUint(item.N, 10)
	case jsonread.ItemNumber:
		return "#"
	case jsonread.ItemStr:
		return "s" + showRequestBytes(item.S)
	case jsonread.ItemKey:
		return "k" + showRequestBytes(item.S)
	case jsonread.ItemArrOpen:
		return "["
	case jsonread.ItemArrClose:
		return "]"
	case jsonread.ItemObjOpen:
		return "{"
	case jsonread.ItemObjClose:
		return "}"
	}
	panic(fmt.Sprintf("bad item %#v", item))
}

func showItems(items *[]jsonread.Item) string {
	if items == nil {
		return "none"
	}
	words := []string{"items"}
	for _, item := range *items {
		words = append(words, showItem(item))
	}
	return strings.Join(words, " ")
}

func showResponse(head string, r httpformat.Response) string {
	return fmt.Sprintf("%s %d %s", head, r.Status, showRequestBytes(r.Body))
}

func refused(err error) (httpformat.Response, bool) {
	answer, ok := errors.AsType[*leanfran.ExceptError[httpformat.Response]](err)
	if !ok {
		return httpformat.Response{}, false
	}
	return answer.Value, true
}

func requestCommand(t *testing.T, words []string) kernel.Command {
	t.Helper()
	switch {
	case len(words) == 2 && words[0] == "set":
		return kernel.CommandSet{Value: requestNumber(t, words[1])}
	case len(words) == 3 && words[0] == "apply":
		if op, ok := opNamed(words[1]); ok {
			return kernel.CommandApply{Op: op, Arg: requestNumber(t, words[2])}
		}
	case len(words) == 1 && words[0] == "get":
		return kernel.CommandGet{}
	}
	t.Fatalf("bad command %v", words)
	return nil
}

func showCommand(cmd kernel.Command) string {
	switch cmd := cmd.(type) {
	case kernel.CommandSet:
		return fmt.Sprintf("set %d", cmd.Value)
	case kernel.CommandApply:
		for _, name := range []string{"add", "sub", "mul", "div"} {
			if op, _ := opNamed(name); op == cmd.Op {
				return fmt.Sprintf("apply %s %d", name, cmd.Arg)
			}
		}
	case kernel.CommandGet:
		return "get"
	}
	panic(fmt.Sprintf("bad command %#v", cmd))
}

func showAuth(bearer httpformat.Bearer, err error) string {
	if answer, ok := refused(err); ok {
		return showResponse("err", answer)
	}
	if err != nil {
		panic(err)
	}
	return fmt.Sprintf("ok %d %d %d %s %s", bearer.Tenant, bearer.User, bearer.Exp,
		showRequestBytes(bearer.Payload), showRequestBytes(bearer.Sig))
}

type requestCounts struct{ utf8, compared int }

func runRequestLine(t *testing.T, line string, counts *requestCounts) string {
	t.Helper()
	words := strings.Split(line, " ")
	switch {
	case len(words) == 2 && words[0] == "read":
		input := requestBytes(t, words[1])
		items := jsonread.Read(input)
		if utf8.Valid(input) {
			counts.utf8++
			fromString, err := jsonread.ReadString(string(input))
			if err != nil || showItems(fromString) != showItems(items) {
				t.Fatalf("ReadString of %s: %s, %v", line, showItems(fromString), err)
			}
			if !surrogateEscape.Match(input) {
				counts.compared++
				if (items != nil) != json.Valid(input) {
					t.Fatalf("encoding/json on %s: %v", line, json.Valid(input))
				}
			}
		}
		return showItems(items)
	case len(words) == 2 && words[0] == "auth" && words[1] == "-":
		return showAuth(httpformat.Authenticate(nil))
	case len(words) == 2 && words[0] == "auth":
		header := string(requestBytes(t, words[1]))
		return showAuth(httpformat.Authenticate(&header))
	case len(words) == 6 && words[0] == "request":
		var body httpformat.Body
		switch words[5] {
		case "notutf8":
			body = httpformat.BodyNotUtf8{}
		case "toolarge":
			body = httpformat.BodyTooLarge{}
		case "unreadable":
			body = httpformat.BodyUnreadable{}
		default:
			body = httpformat.BodyText{S: string(requestBytes(t, words[5]))}
		}
		call, err := wire.Request(requestNumber(t, words[1]), requestNumber(t, words[2]),
			requestNumber(t, words[3]), requestNumber(t, words[4]), body)
		if answer, ok := refused(err); ok {
			return showResponse("err", answer)
		}
		if err != nil {
			t.Fatal(err)
		}
		return fmt.Sprintf("ok %d %d %s", call.Actor.Org, call.Actor.User, showCommand(call.Cmd))
	case len(words) == 3 && words[0] == "respond" && words[1] == "ok":
		return showResponse("resp", Calculator{}.Respond(kernel.Reply{V: requestNumber(t, words[2])}, nil))
	case len(words) == 3 && words[0] == "respond" && words[1] == "err":
		refusals := map[string]kernel.Error{
			"overflow": kernel.ErrorOverflow(), "underflow": kernel.ErrorUnderflow(),
			"division_by_zero": kernel.ErrorDivByZero(),
		}
		refusal, ok := refusals[words[2]]
		if !ok {
			t.Fatalf("bad refusal %s", words[2])
		}
		return showResponse("resp", Calculator{}.Respond(kernel.Reply{}, &refusal))
	case len(words) == 2 && words[0] == "failure":
		failures := map[string]httpformat.Failure{
			"bad_signature": httpformat.FailureBadSignature(), "conflict": httpformat.FailureConflict(),
			"stopped": httpformat.FailureStopped(), "retries_exhausted": httpformat.FailureRetriesExhausted(),
			"database": httpformat.FailureDatabase(), "commit_unknown": httpformat.FailureCommitUnknown(),
			"broken": httpformat.FailureBroken(),
		}
		failure, ok := failures[words[1]]
		if !ok {
			t.Fatalf("bad failure %s", words[1])
		}
		return showResponse("resp", httpformat.Failed(failure))
	case len(words) >= 2 && words[0] == "fingerprint":
		return "bytes " + showRequestBytes(Calculator{}.Fingerprint(requestCommand(t, words[1:])))
	case len(words) == 2 && words[0] == "scope":
		actor := kernel.Principal{Org: 0, User: requestNumber(t, words[1])}
		return "text " + showRequestBytes([]byte(Calculator{}.Scope(actor)))
	}
	t.Fatalf("bad line %s", line)
	return ""
}

// The generated Go JSON reader, the functions on requests and responses and the calculator's
// functions on the wire against those run natively by Lean (`request-oracle`), on the shared
// lines. The line format is described in `lean/RequestOracle.lean`. A text to read that is UTF-8
// is also read by ReadString, which must read what Read reads, and its acceptance is compared
// with that of encoding/json.
func TestGeneratedGoRequestFunctionsAgreeWithLean(t *testing.T) {
	path, ok := os.LookupEnv("LEANGAGE_REQUEST_ORACLE")
	if !ok {
		t.Fatal("LEANGAGE_REQUEST_ORACLE is required")
	}
	text, err := os.ReadFile(requestCases)
	if err != nil {
		t.Fatal(err)
	}
	oracle := exec.Command(path)
	oracle.Stdin = bytes.NewReader(text)
	theirs, err := oracle.Output()
	if err != nil {
		t.Fatal(err)
	}
	lines := strings.Split(strings.TrimSuffix(string(text), "\n"), "\n")
	want := strings.Split(strings.TrimSuffix(string(theirs), "\n"), "\n")
	if len(lines) != len(want) {
		t.Fatalf("%d lines, %d answers", len(lines), len(want))
	}
	var counts requestCounts
	for i, line := range lines {
		if got := runRequestLine(t, line, &counts); got != want[i] {
			t.Fatalf("line %d: %s\n got %s\nwant %s", i+1, line, got, want[i])
		}
	}
	if counts.utf8 <= 800 || counts.compared <= 700 {
		t.Fatalf("%d texts are UTF-8, %d compared", counts.utf8, counts.compared)
	}
}
