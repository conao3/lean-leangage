package leanharbor

import "testing"

type who struct{ tenant, user uint64 }

// counter adds the command to the tenant's number, refuses a negative command and panics on
// zero.
type counter struct{}

func (counter) Init() int { return 0 }

func (counter) Tenant(actor who) uint64 { return actor.tenant }

func (counter) Transition(_ who, snap int, cmd int) (int, int, *string) {
	if cmd == 0 {
		panic("zero")
	}
	if cmd < 0 {
		refusal := "negative"
		return 0, 0, &refusal
	}
	return cmd, snap + cmd, nil
}

func (counter) Apply(snap int, ws int) int { return snap + ws }

func (c counter) Scoped(run func(Kernel[who, int, int, int, int, string])) { run(c) }

func key(scope, key string, fingerprint string) *Idempotency {
	return &Idempotency{Scope: scope, Key: key, Fingerprint: []byte(fingerprint)}
}

func TestIdempotency(t *testing.T) {
	engine := NewMemoryEngine(counter{})
	alice := who{tenant: 1, user: 1}
	steps := []struct {
		actor       who
		cmd         int
		idempotency *Idempotency
		reply       int
		refused     bool
		err         error
	}{
		{alice, 5, nil, 5, false, nil},
		{alice, 2, key("u1", "a", "2"), 7, false, nil},
		{alice, 2, key("u1", "a", "2"), 7, false, nil},
		{alice, 3, key("u1", "a", "3"), 0, false, ErrIdempotencyConflict},
		{alice, 2, key("u2", "a", "2"), 9, false, nil},
		{who{tenant: 2, user: 1}, 2, key("u1", "a", "2"), 2, false, nil},
		{alice, -1, key("u1", "b", "-1"), 0, true, nil},
		{alice, 1, key("u1", "b", "1"), 10, false, nil},
		{alice, 1, nil, 11, false, nil},
	}
	for i, step := range steps {
		reply, refusal, err := engine.Execute(step.actor, step.cmd, step.idempotency)
		if reply != step.reply || (refusal != nil) != step.refused || err != step.err {
			t.Fatalf("step %d: got %d, %v, %v", i, reply, refusal, err)
		}
	}
}

func TestStopsAfterPanic(t *testing.T) {
	engine := NewMemoryEngine(counter{})
	actor := who{tenant: 1, user: 1}
	func() {
		defer func() { _ = recover() }()
		_, _, _ = engine.Execute(actor, 0, nil)
		t.Fatal("the command returned")
	}()
	if _, _, err := engine.Execute(actor, 1, nil); err != ErrStopped {
		t.Fatalf("got %v", err)
	}
}
