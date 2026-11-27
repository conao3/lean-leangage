package calculator

import (
	"bytes"
	"encoding/hex"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"testing"

	"github.com/conao3/leanfran-go"

	"github.com/conao3/lean-leangage/go/calculator/gen/kernel"
	"github.com/conao3/lean-leangage/go/calculator/gen/wire"
	"github.com/conao3/lean-leangage/go/leangage"
	"github.com/conao3/lean-leangage/go/leangage/gen/httpformat"
	"github.com/conao3/lean-leangage/go/leangage/gen/jsonlexemes"
)

const requestCases = "../../testdata/request-cases.txt"

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

func showLexeme(t *testing.T, lexeme jsonlexemes.Lexeme) string {
	t.Helper()
	switch lexeme := lexeme.(type) {
	case jsonlexemes.LexemeNull:
		return "n"
	case jsonlexemes.LexemeBool:
		if lexeme.B {
			return "t"
		}
		return "f"
	case jsonlexemes.LexemeNumber:
		n, err := jsonlexemes.NumberOf(lexeme.Text)
		if err != nil {
			t.Fatal(err)
		}
		if n == nil {
			return "#"
		}
		return "u" + strconv.FormatUint(*n, 10)
	case jsonlexemes.LexemeStr:
		return "s" + showRequestBytes([]byte(lexeme.S))
	case jsonlexemes.LexemeKey:
		return "k" + showRequestBytes([]byte(lexeme.S))
	case jsonlexemes.LexemeArrOpen:
		return "["
	case jsonlexemes.LexemeArrClose:
		return "]"
	case jsonlexemes.LexemeObjOpen:
		return "{"
	case jsonlexemes.LexemeObjClose:
		return "}"
	}
	panic(fmt.Sprintf("bad token %#v", lexeme))
}

func showTokens(t *testing.T, input []byte) string {
	t.Helper()
	tokens, ok := leangage.Tokens(input)
	if !ok {
		return "none"
	}
	lexemes, err := unpacked(tokens)
	if err != nil {
		t.Fatal(err)
	}
	words := []string{"tokens"}
	for _, lexeme := range lexemes {
		words = append(words, showLexeme(t, lexeme))
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

func runRequestLine(t *testing.T, line string) string {
	t.Helper()
	words := strings.Split(line, " ")
	switch {
	case len(words) == 2 && words[0] == "tokens":
		return showTokens(t, requestBytes(t, words[1]))
	case len(words) == 2 && words[0] == "auth" && words[1] == "-":
		return showAuth(httpformat.Authenticate(nil))
	case len(words) == 2 && words[0] == "auth":
		header := string(requestBytes(t, words[1]))
		return showAuth(httpformat.Authenticate(&header))
	case len(words) == 6 && words[0] == "request":
		var body httpformat.Body
		switch words[5] {
		case "toolarge":
			body = httpformat.BodyTooLarge{}
		case "unreadable":
			body = httpformat.BodyUnreadable{}
		default:
			body = leangage.BodyOf(requestBytes(t, words[5]))
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

// The tokens encoding/json reads, the functions on requests and responses and the calculator's
// functions on the wire against those run natively by Lean (`request-oracle`), on the shared
// lines. The line format is described in `lean/RequestOracle.lean`.
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
	for i, line := range lines {
		if got := runRequestLine(t, line); got != want[i] {
			t.Errorf("line %d: %s\n got %s\nwant %s", i+1, line, got, want[i])
		}
	}
}

// A member whose name differs from `cmd` in case is another member: the tokens keep the name as
// it is written.
func TestUpperCaseMemberNameIsNotCmd(t *testing.T) {
	_, err := wire.Request(1, 1, 1, 0, leangage.BodyOf([]byte(`{"CMD":"get"}`)))
	answer, ok := refused(err)
	if !ok || answer.Status != 400 || string(answer.Body) != "{\"error\":\"missing field `cmd`\"}" {
		t.Fatalf("got %v %s", err, answer.Body)
	}
	call, err := wire.Request(1, 1, 1, 0, leangage.BodyOf([]byte(`{"cmd":"get"}`)))
	if err != nil || call.Cmd != kernel.Command(kernel.CommandGet{}) {
		t.Fatalf("got %v %v", call, err)
	}
}

// unpacked is the tokens of a packed text, one by one.
func unpacked(packed string) ([]jsonlexemes.Lexeme, error) {
	lexemes, err := jsonlexemes.Unpack(packed)
	if err != nil || lexemes == nil {
		return nil, err
	}
	return *lexemes, nil
}
