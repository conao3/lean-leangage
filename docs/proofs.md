# What is proved, and what is trusted

## Proved

Proved in Lean, about the definitions that are generated and run:

- the 6 theorems of [`Calculator.Proofs`](calculator.md), for the calculator kernel. The 3 servers call `transition` and
  `apply`;
- the guard's theorems of [`Leangage.AuthzProofs`](notes.md), for every kernel and policy, and the notes theorems, for the notes
  kernel. Its `transition` is `handle` behind `guardViewed`, and the 3 servers call it;
- `Leangage.Kernel.Run.inv`: a property that holds for the initial snapshot and is kept by
  every accepted command holds in every snapshot a tenant can reach. `Obligation.Invariant.run`
  states it for a property that satisfies `Obligation.Invariant`;
- for the SQL compiler `Leangage.Sql` (`plan`, `compile`, `select`, `create`, `render`,
  `valid`), which is generated to the 3 servers and which the 3 PostgreSQL engines call for
  every statement on a kernel's tables:
  - `lexName_quote`: a quoted name followed by any character but `"` reads back as exactly that
    name, under PostgreSQL's rule for quoted identifiers written as a lexer on characters;
  - `compile_params`, `select_params`: the parameters of every compiled statement are the tenant
    (`$1`), then the statement's values in order;
  - `compile_placeholders`, `select_placeholders`: the compiled statement refers to `$1` … `$n`
    for its `n` parameters, each once and in order. The statement is the `Sql` value that `render`
    prints, and `render_spec` fixes the text of each part;
  - `compile_erase`, `select_erase`: the compiled statement is the same for every tenant and for
    every value of the same kinds;
  - `render_spec`, `valid_iff`, `compile_spec`, `select_spec`, `create_spec`, `plan_spec`: the
    generated functions equal definitions written another way (the text as lists of characters,
    the schema checks as propositions);
  - against the model of PostgreSQL in `Leangage.Sql.Model`, on tables that `create` made:
    - `compile_sound`: a compiled statement runs, the tables stay as `create` made them, the
      tenant's rows change as `exec` says, and no other tenant's rows and no table outside the
      schema change. `compileAll_sound` states the same for a list of statements;
    - `select_sound`: a compiled `SELECT` returns the tenant's rows of the table that pass the
      filter, each once, in any order. `lists_of_selects`: a `SELECT` of every table lists the
      tenant's rows;
    - `create_sound`: creating the tables of a valid schema in a database without them gives
      tables that match the schema, with no row for any tenant, and changes no other table.
      `create_kept`: tables that exist are kept as they are;
    - `tenant_isolation` (`TenantIsolation`), for every schema `valid` accepts: statements
      compiled for one tenant leave every other tenant's rows as they were, and a compiled
      `SELECT` returns the same rows, up to order, from 2 databases that hold the same rows for
      its tenant;
- for every kernel with a `Leangage.Storage`, against the same model. `Storage.Stored` is what
  an engine does to one tenant on a shared database, from tables that match the schema and hold no
  row for the tenant: load the snapshot from the rows a compiled `SELECT` of each table returned,
  run an accepted command of any principal on it, and run the statements compiled from its write
  set, with statements compiled for other tenants in between. Two more of its rules are those of
  the snapshot an engine remembers: `loaded` holds the snapshot loaded from the rows, and `cached`
  runs an accepted command on the snapshot held, without a `SELECT`, and runs the statements of
  its write set. For every database and snapshot that `Stored` relates:
  - `stored_view`: the tenant's rows are those of the snapshot held, which `apply` computed or
    `load` built, and the tables stay as `create` made them;
  - `stored_load`: loading the tenant's rows gives back a snapshot that stands for the same rows;
  - `stored_inv`: a property of `init`, kept by every accepted command, that holds for a snapshot
    when it holds for one standing for the same rows, holds for every snapshot loaded;
  - `stored_commit`: the `SELECT`s of the tables return rows, the rows load, and compiled
    statements run;
  - `create_stored`: creating the tables in a database without them starts every tenant from
    `init`;
- for the calculator's table (`Calculator.Store`: `tables`, `toRow`, `fromRow`, `writes`,
  `storeAll`, `load`), which is generated to the 3 servers and which the 3 calculator
  servers call through the PostgreSQL engines:
  - `fromRow_toRow`, `toRow_fromRow`: the laws of `Row`;
  - `writes_compile`: every write set compiles, for every tenant;
  - `enc_apply`, `load_enc`: the obligations of the calculator's `storage`, so the theorems above
    hold for the calculator;
  - `stored_lookup`, `stored_transition`: the snapshot loaded from a tenant's rows stores a number
    for the same users, with the same values, as the snapshot the engine holds, and answers every
    command of every principal as that snapshot does. They compare the numbers the 2 snapshots
    hold; that the 2 are the same tree isn't proved;
  - `stored_commit`: every commit goes through: the `SELECT` returns rows, they load, and every
    write set compiles and runs;
- for the notes' tables (`Notes.Store`: `tables`, `memberRow`, `memberOfRow`, `noteRow`,
  `noteOfRow`, `write`, `writes`, `load`), which are generated to the 3 servers and which the
  Rust notes server calls through the PostgreSQL engine:
  - `memberOfRow_memberRow`, `memberRow_memberOfRow`, `noteOfRow_noteRow`, `noteRow_noteOfRow`:
    the laws of `Row`;
  - `writes_compile`: every write set compiles, for every tenant;
  - `enc_apply`, `load_enc`: the obligations of the notes' `storage`, so the theorems above hold
    for the notes;
  - `stored_keyed`, `stored_load`: every snapshot an engine stores, and every snapshot it loads
    from a tenant's rows, has unique keys;
  - `stored_transition`: the snapshot loaded from a tenant's rows answers every command of every
    principal as the snapshot the engine holds does. The 2 may hold their rows in different
    orders; `transition_congr` makes the replies equal;
  - `stored_authorized`: a command accepted on the snapshot loaded from a tenant's rows is
    authorized against the snapshot the engine holds, as `transition_authorized` states it: a
    command that writes is `handle`'s result on that snapshot with every write permitted and every
    disclosed row stored and visible, and a read-only command is `handle`'s result on the caller's
    view of it, with no writes. So every write set an engine stores is one the guard permits in
    the state the tenant's rows stand for;
  - `stored_noninterference`: a read-only command of a principal gives the same result on the
    snapshots loaded from 2 databases, or 2 tenants, when the rows the principal may see stand
    for the same rows;
  - `accepted_no_nul`: no body that an accepted command writes holds NUL;
  - `stored_commit`: every commit goes through: the `SELECT`s return rows, they load, and every
    write set compiles and runs;
- for the token functions `Leangage.Token` (`encodePayload`, `join`, `parseString`), which the
  3 servers call to issue a bearer token and which `authenticate` calls to read one:
  - `parseString_spec`: `parseString`, which reads a token as a `String` and returns its fields
    with the bytes in arrays, returns what `parse` returns for the bytes of the string. So the
    theorems about `parse` below hold for what the servers run, and `parseString_join`,
    `parseString_sound` and `parseString_canon` state them for `parseString`;
  - `parse_join`: parsing the token that `join` makes of `encodePayload t u e` and any signature
    gives back `t`, `u`, `e`, that payload and that signature;
  - `parse_sound`, `parse_canon`: a token that `parse` accepts is `join` of its payload and its
    signature, and the payload is `encodePayload` of the tenant, the user and the expiry that
    `parse` returns. So a token has one spelling (no leading zero, sign, uppercase hexadecimal or
    other version is accepted), and the bytes the server checks the signature over are the bytes
    before the last dot;
  - `encodePayload_injective`: a payload determines the tenant, the user and the expiry, so a
    signature over it binds one reading;
  - `splitDot_spec`, `hexValue_spec`, `join_spec`, `value_decimal`, `number_decimal`,
    `splitDot_dotFrom`, `numberAt_spec`, `unhexAt_spec` and the others in
    `Leangage.Token.Proofs`: the generated helpers equal definitions written another way, or
    read back what they write.
- for the JSON writer `Leangage.Json` (`escape`, `write`, `writeArray`), which writes every
  JSON body that the 3 servers send:
  - `writeArray_spec`: `writeArray`, which takes tokens whose strings are `String`s and writes
    into an array, writes the bytes that `write` writes for the same tokens with the bytes of
    each string. So the theorems about `write` below hold for what the servers run, and
    `writeArray_value` states `write_value` for `writeArray`;
  - `write_value`: `write` of the tokens of a JSON value is `Value.print` of the value, a printer
    over the tree: `null`, `true`, `false`, numbers in decimal, quoted strings, and arrays and
    objects with their elements and members separated by commas;
  - `write_spec`: on any list of tokens, a document or not, `write` puts a comma before each token
    that follows a value and doesn't close an array or an object, and writes each token as
    `printToks` says;
  - `lex_escape`: a JSON string lexer that reads `escape s` and then a quote returns `s` and the
    bytes after that quote, whatever they are. So no byte of a string ends it early or changes
    what it reads as;
  - `escape_no_control`: an escaped string has no byte below 0x20;
  - `escapeByte_spec`, `tokBytes_spec`, `writeFrom_spec`, `decimal_spec`, `pushEscaped_spec`,
    `pushTok_spec` and the others in `Leangage.Json.Proofs`: the generated helpers equal
    definitions written another way.
- for the calculator's bodies (`encodeReplyArray`, `encodeErrorArray` in `Calculator.Kernel`),
  which the 3 servers send for every accepted and refused command: `encodeReplyArray_spec`
  and `encodeErrorArray_spec` say that they are `Value.print` of `{"value": v}` and of
  `{"error": name}`, with the names `overflow`, `underflow` and `division_by_zero`, as
  `encodeReply_spec` and `encodeError_spec` say of `encodeReply` and `encodeError`.
- for the functions on the tokens of a JSON text `Leangage.Json.Lexemes` (`unpack`, `texts`,
  `splitAt`, `lengthOf`, `zip`, `numberOf`, `scalar`, `members`, `object`), which the 3
  calculator servers and the notes server run on the tokens of a body:
  - `unpack_pack`, `unpack_iff`, `unpack_spec`, `texts_packTexts`, `lengthOf_toDigits`: a
    conversion hands over one text, the kinds of the tokens (`{`, `}`, `[`, `]`, `n` for null,
    `t` and `f` for true and false, `#` for a number, `s` for a string, `k` for a key), a line
    feed, and the texts of the numbers, the strings and the keys, each but the last after the
    count of its characters in decimal and a colon (`pack`). So a body crosses into the generated
    code as 1 text whatever its number of tokens. `unpack` gives back, one by one, the tokens
    that `pack` packs, and it gives tokens for no other text: a count that is not the decimal of
    a number, that is longer than what is left, or characters left over give none;
  - `numberOf_iff`, `numberOf_decimalText`, `numberOf_some`: a number token has the value `n`
    exactly when the bytes of its text are the decimal of the `UInt64` `n`, so the decimal of
    every number below 2^64 has its value (`decimalText`, `bytesOf_decimalText`), and a text with
    a sign, a fraction, an exponent or a leading zero and a text that spells 2^64 or more have
    none;
  - `scalar_spec`: the value of a token that is a value by itself; a number token is `num n`
    when `numberOf` gives `n` and `number` otherwise, and a string is its text;
  - `object_iff`, `object_objectLexemes`, `object_shape`, `members_object`: `object` gives
    members exactly for the tokens of an object whose values are values by themselves, and the
    members are the names with the values of those tokens, in the order of the text, a member
    twice as two members.

  The theorems of `Calculator.Wire` and `Notes.Wire` below start from the tokens. That the
  tokens are those of the text of the body is trusted to the JSON library and the conversion
  file: they hand over `pack ls` for the tokens `ls` of the text, in its order, a number as the
  text of its token, a string and a key as their text; for the text that spells a command `c`
  that is `pack (lexemesOf c)`, and for the text `encodeReply` writes for a reply `r` it is
  `pack ((replyToks r).map Lexeme.ofStrTok)`, the tokens it writes with a number as its
  decimal;
- for the functions on requests and responses `Leangage.Http` (`authenticate`, `admit`,
  `failed`, `refuse`). The 3 servers call `authenticate` for every `Authorization` header they
  have not accepted before, and `failed` for every request the engine fails; the calculator's
  `request` starts with `admit`:
  - `refuse_status`, `refuse_body`: `refuse status message` has that status and the body
    `Value.print` of `{"error": message}`. Every answer below is one;
  - `authenticate_missing`, `authenticate_not_bearer`, `authenticate_bearer`: a request without
    the header is answered 401 `missing authorization header`; a header that is not `Bearer `
    followed by a text is answered 401 `authorization is not a bearer token`; the header
    `Bearer <t>` is answered 401 `malformed token` when `parseString` refuses `t`, and gives the
    fields `parseString t` returns otherwise;
  - `authenticate_ok_iff`, `authenticate_sound`, `authenticate_issued`: the accepted headers are
    exactly `Bearer <t>` with `t` accepted by `parseString`; for them `t` is `join` of the
    payload and the tag returned, and the payload is `encodePayload` of the tenant, the user and
    the expiry returned, so the bytes a server computes the HMAC over are every byte of the token
    before its last dot and fix the claims; the header of an issued token gives back what was
    signed;
  - `admit_expired`, `admit_json`, `admit_not_json`: a token whose expiry is before the time
    given is answered 401 `token expired` whatever the body; otherwise the tokens of the body
    pass, and a body the JSON library refuses, one longer than the server reads and
    one that cannot be read are answered 400 `body is not JSON`, 413 `request body too large` and
    400 `request body cannot be read`;
  - `failed_spec`: a tag that is not the HMAC of its payload is answered 401
    `bad token signature`, a reused idempotency key 422, a stopped engine, exhausted retries and
    a failure of the database 503, a lost COMMIT and a broken engine 500, each with its message;
- for the calculator's functions on the wire `Calculator.Wire` (`request`, `respond`,
  `fingerprint`, `scope`), which the 3 calculator servers call for every request:
  - `decode_encode`, `request_encode`: a body whose tokens are `pack (lexemesOf c)`, those of
    the text that spells the command `c` with a number as its decimal, sent with a token that has
    not expired, gives the engine the command `c` for the principal of the token's tenant and
    user (`request_actor`);
  - `answerOf_spec`, `call_spec`, `request_call`, `request_answer`: `answerOf`, `actorOf` and
    `cmdOf` take the result of `request` apart, the answer when there is one and otherwise the
    principal and the command of the call. The Python server reads the result through them and
    hands the principal and the command to the kernel as the Lean values they are;
  - `decode_eq`, `spelled_iff`, `spelled_sound`, `spelled_lexemesOf`, `numbered_iff`: `decode`
    reads a command whose members come in the order `cmd`, `value` or `cmd`, `op`, `arg` from the
    start of the packed text and the number at its end (`spelled`, which gives `c` exactly for
    `pack (lexemesOf c)`), and for every other body unpacks the tokens, collects their members
    and looks each up by its name (`decodeObject`); `decode packed` is `decodeObject` of the
    tokens `unpack packed` gives on every body, so the theorems below hold for both paths;
  - `decode_malformed`, `decode_notJson_iff`: a text that no list of tokens packs to is answered
    400 `body is not JSON`, and no other text is;
  - `decode_ok_iff`, `decodeMembers_ok_iff`, `decode_object`, `decode_not_object`: a packed text
    is decoded to `c` exactly when `object` gives members for the tokens it unpacks to, as many
    as `c` has fields and with each field among them. So the members may come in any order, and an object with another
    member, with a member twice or with a member whose value is an array or an object is refused;
  - `decodeMembers_missingCmd_iff`, `refusalMessage_spec`: the refusal ``missing field `cmd` ``
    is that of the objects without that member, and each refusal has its message;
  - `decodeMembers_badValue_iff`, `decodeMembers_badArg_iff`: the refusal about `value` is that
    of the objects of 2 members with `"cmd":"set"` whose `value` is not a number below 2^64 in
    decimal digits, and the one about `arg` that of the objects of 3 members with
    `"cmd":"apply"` and an `op` that names an operation whose `arg` is not such a number. Every
    other refused object is `not a calculator command`;
  - `request_expired`, `request_json`, `request_not_json`, `request_refusal`: an expired token
    is answered 401 whatever the body; otherwise the tokens of a body are answered with the
    command they decode to or 400 with the message of the refusal; every answer of
    `request` has the status 400, 401 or 413 and a body `{"error": message}`;
  - `respond_ok`, `respond_error`: an accepted command is answered 200 with `Value.print` of
    `{"value": v}`, a refused one 422 with `Value.print` of `{"error": name}`;
  - `fingerprint_spec`, `fingerprint_injective`: the fingerprint of a command is the text
    `Set { value: 6 }`, `Apply { op: Mul, arg: 7 }` or `Get`, and different commands have
    different fingerprints;
  - `scope_injective`: 2 principals have the same scope exactly when they have the same user.
- for the notes' functions on the wire `Notes.Wire` (`request`, `respond`, `fingerprint`,
  `scope`, `encodeReply`, `decodeReply`), which the Rust notes server calls for every request:
  - `decode_encode`, `request_encode`: a body whose tokens are `pack (lexemesOf c)`, those of
    the text that spells the command `c` with a number as its decimal, sent with a token that has
    not expired, gives the engine the command `c` for the principal of the token's organization
    and user (`request_actor`);
  - `decode_ok_iff`, `decodeMembers_ok_iff`, `decode_object`, `decode_not_object`,
    `decode_malformed`, `decode_notJson_iff`: a packed text is decoded to `c` exactly when
    `object` gives members for the tokens it unpacks to, as many as `c` has fields and with each
    field among them, and a text that no list of tokens packs to is answered 400
    `body is not JSON`, so the members may come in any order, and an object with another
    member, with a member twice or with a member whose value is an array or an object is refused.
    The body of `put_note` is the text of its string token;
  - `decodeMembers_missingCmd_iff`, `decodeMembers_notCommand_iff`, `refusalMessage_spec`: the
    refusal ``missing field `cmd` `` is that of the objects without that member, and
    `not a notes command` that of the objects with a member `cmd` whose members are the fields
    of no command;
  - `request_expired`, `request_json`, `request_not_json`, `request_refusal`: an expired token
    is answered 401 whatever the body; otherwise the tokens of a body are answered with the
    command they decode to or 400 with the message of the refusal; every answer of
    `request` has the status 400, 401 or 413 and a body `{"error": message}`;
  - `respond_ok`, `encodeReply_spec`, `respond_error`: an accepted command is answered 200 with
    `Value.print` of `replyValue` (`{"done":true}`, `{"note":…}`, `{"notes":[…]}`,
    `{"members":[…]}`, the members of a note and of a member in the order of their keys), the
    guard's refusal 403, `notFound` 404 and `badText` 422, each with `Value.print` of
    `{"error": name}`;
  - `decodeReply_encode`, `replyOf_lexemes`, `decodeReply_spec`, `decodeReply_none`:
    `decodeReply` reads the tokens of a stored reply, which the server's JSON library reads from
    the stored bytes. The tokens of the text `encodeReply` writes for the reply `r`
    (`pack ((replyToks r).map Lexeme.ofStrTok)`: the tokens it writes, a number as its decimal,
    packed as a conversion packs them) are read back as `r`, so a request repeated under
    an idempotency key gets the reply the engine stored; stored bytes the library refuses are no
    reply;
  - `fingerprint_spec`, `fingerprint_injective`: the fingerprint of a command is the text
    `AddMember { user: 2, admin: false }`, `RemoveMember { user: 2 }`,
    `PutNote { id: 7, body: "text", shared: true }` with the body escaped as in a JSON string,
    `DeleteNote { id: 7 }`, `ReadNote { id: 7 }`, `ListNotes` or `ListMembers`, and different
    commands have different fingerprints;
  - `scope_injective`: 2 principals have the same scope exactly when they have the same user.

## Checked

Checked by `make check`, not proved:

- **The theorems state the framework's statements.** `Leangage.Obligation` fixes statements
  that have the same form for every kernel: `ReadOnlySound k writes` (whenever `readOnly c` is
  `true` and `transition` accepts `c`, `writes` of the write set is empty) and `Invariant k I`
  (`I` holds for `init` and is kept by every accepted command). `#obligations k`
  ([`audit/Audit/Obligations.lean`](../audit/Audit/Obligations.lean)) fails the build unless a
  theorem's type is definitionally equal, in Lean's kernel, to `ReadOnlySound k _`, and to
  `Invariant k I` for each `I` listed after `invariant`, and that theorem depends only on
  `propext`, `Classical.choice` and `Quot.sound`. It searches the theorems of the file and of the
  imported modules outside `Init`, `Std`, `Lean` and `Lake`. The write list is the kernel's
  choice: the check prints it, and a list that is always empty would pass. For the calculator,
  `#obligations Calculator.Kernel.kernel` finds `read_only_sound` with the write list
  `fun w => w.toList`; the calculator lists no invariant. For the notes,
  `#obligations Notes.Kernel.kernel invariant Notes.Kernel.Keyed` finds `read_only_sound` with the
  write list `fun ws => ws` and `keyed_invariant` (no 2 members share a user id and no 2 notes
  an id). The PostgreSQL engines rely on `ReadOnlySound`: they run a command that `readOnly`
  marks, sent without an idempotency key, in a read-only transaction, and fail it if its write set
  stores a row (item 6 of their contract). The memory engines run every command the same way.
  `make check` also builds the files in [`audit/fail/`](../audit/fail), a kernel without the
  theorem, with a theorem that has one more hypothesis, with a listed invariant that no theorem
  states, and with an invariant left as a hole, and requires each to fail with the check's error;
- **The theorems constrain the kernel.** [leanassay](https://github.com/conao3/lean-leanassay)
  breaks functions in small ways and runs the theorems on each broken version. For the
  calculator, it breaks `transition`, `apply`, `compute` and the 3 functions of the trie in
  167 ways: 132 are rejected, 5 behave the same on every input tried, 30 don't compile, and none
  satisfies every theorem while changing an output. The same holds for the 26 functions of the SQL
  compiler (285 ways: 241 rejected, 6 behave the same, 38 don't compile), the 20 functions of
  the token format (453 ways: 387 rejected, 15 behave the same, 51 don't compile), the 15
  functions of the JSON writer (524 ways: 454 rejected, 6 behave the same, 64 don't compile), the
  8 functions that make the calculator's bodies (111 ways, all rejected), the 4 functions of
  `Leangage.Http` that it can break (95 ways: 89 rejected, 6 don't compile; `refuse` is one
  constructor applied to its arguments, and it makes no broken version of it), the 15 functions
  of `Calculator.Wire` (370 ways: 339 rejected, 3 behave the same, 28 don't compile), 17
  functions of `Notes.Wire` (553 ways: 478 rejected, 6 behave the same, 69 don't compile), the 6
  functions of the calculator's table (25 ways: 20 rejected, 5 don't compile) and the 8 functions of the notes'
  tables (46 ways: 30 rejected, 16 don't compile). For the guard, it breaks `guard`, `guardViewed` and the 4 checks in 28 ways and runs `guard_eq`,
  `guard_viewed_eq` and the lemmas about the checks on random kernels and policies: 22 are
  rejected, 1 behaves the same, 5 don't compile, and none satisfies every theorem while changing
  an output. For the notes, it breaks `handle`, `apply`, `applyWrite`, `textOk`, the 4
  functions on the row lists, the 4 functions that sort the listings and the 7 functions of
  the policy in 217 ways: 141 are rejected, 5 behave the same, 71 don't compile, and none
  satisfies every theorem while changing an output.
  The notes' `transition` is one call of `guardViewed`, and no edit of it compiles.
  For the functions on the tokens of a JSON text, it breaks `unpack`, `texts`, `splitAt`,
  `lengthOf`, `isKind`, `hasText`, `zip`, `numberOf`, `scalar`, `members` and `object` in 146
  ways (115 rejected, 31 don't compile) and runs the theorems on the decimals of numbers up to
  2^64 − 1 and texts close to one (a leading zero, a sign, a fraction, an exponent, 2^64 and
  numbers of 20 and 21 digits), on the tokens of an object of 2 members and lists of tokens close
  to one, and on their packed texts and texts close to one: a character added or dropped, a count
  with a leading zero, a count longer than the text, a kind that is none. The audits of
  `Calculator.Wire` and `Notes.Wire` run `request` and `decodeReply` on the packed tokens of the
  spellings of the commands and of the replies and on texts close to one.
- **The tables, as PostgreSQL receives them.** `tables_create` evaluates, in Lean's kernel, the
  text of the statements that create them. For the calculator:
  `CREATE TABLE IF NOT EXISTS "memories" ("tenant_id" BIGINT NOT NULL, "user" BIGINT NOT NULL, "value" BIGINT NOT NULL, PRIMARY KEY ("tenant_id", "user"))`.
  For the notes:
  `CREATE TABLE IF NOT EXISTS "members" ("tenant_id" BIGINT NOT NULL, "user" BIGINT NOT NULL, "admin" BOOLEAN NOT NULL, PRIMARY KEY ("tenant_id", "user"))`
  and
  `CREATE TABLE IF NOT EXISTS "notes" ("tenant_id" BIGINT NOT NULL, "id" BIGINT NOT NULL, "owner" BIGINT NOT NULL, "shared" BOOLEAN NOT NULL, "body" TEXT NOT NULL, PRIMARY KEY ("tenant_id", "id"))`.
- **The generated code computes what Lean computes.** 5,000 calculator commands (698 refusals,
  values up to 2^64 − 1) and 3,000 notes commands (1,826 refusals: 1,383 denied by the guard, 336
  not found, 107 bodies refused; bodies of characters of 1 to 4 bytes, up to and past 4096 bytes)
  run through the generated Rust, the generated Python and the generated Go give the same output
  as the kernels compiled natively by Lean. 3,024 lines of schemas and statements
  (1,189 compiled statements, 1,481 refused ones, names with `"`, non-ASCII and NUL, values up to
  the bounds of 64 bits) give the same SQL text and parameters in the generated Rust, Python and
  Go as in the compiler compiled natively by Lean. 3,000 token lines (985 issued tokens, 845
  accepted and 1,170 rejected ones: edited bytes, leading zeros, signs, numbers of 2^64 and more,
  uppercase hexadecimal, missing and extra fields) give the same fields and bytes in the generated
  Rust, Python and Go as in the token functions compiled natively by Lean, and the 1,916 tokens
  to read that are UTF-8 give the same through `parseString` (Go's `ParseString` refuses the
  others). 3,000 token lists (1,627 of them JSON documents; 4,903 strings and keys, of which 1,505
  hold control bytes, 257 a `"`, 265 a `\`, 2,992 bytes above 0x7f and 1,436 bytes that aren't
  UTF-8) give the same bytes in the generated Rust, Python and Go as in the writer compiled
  natively by Lean, and the 2,107 lists whose strings are UTF-8 give the same through
  `writeArray`. 3,000 request lines (1,334 JSON texts, of which 574 are read and 760 refused:
  every spelling of a number, of an escape and of the space between tokens, texts with a byte
  removed, inserted or replaced, arrays 100 deep, a member twice, trailing data, `NaN` and
  `Infinity`, a byte order mark, UTF-16; 445 `Authorization` headers, 150 of them
  accepted; 911 requests, 289 of them accepted and 622 answered 400, 401 or 413: the members of
  a command in any order, with and without space, a member missing, added, repeated or renamed
  in upper case, values of other kinds, the numbers 2^64 − 1, 2^64, `01`, `-0`, `1.0` and `1e2`,
  bodies that are not UTF-8, expired tokens; 310 responses, failures, fingerprints and scopes)
  give the same tokens, claims, commands, statuses and bytes in Rust, Python and Go as in the
  functions compiled natively by Lean. The 3 servers read each text and each body with their
  JSON library and their conversion file and give the tokens to the generated functions, and
  the tests print the tokens of a text through the generated `unpack`; the oracle reads
  them with a JSON reader written in Lean
  ([`lean/Oracle/JsonText.lean`](../lean/Oracle/JsonText.lean)), which only the oracles import, and
  packs them with `pack`. So the lists compare what each library hands over with that reader.
  3,000 notes request lines (1,766 requests, 594 of them accepted and 1,172 answered 400, 401 or
  413: the members of a command in any order, a member missing, added, repeated or renamed,
  values of other kinds, bodies with every escape, expired tokens; 504 responses; 385
  fingerprints; 125 scopes; 220 stored replies, of which `decodeReply` reads 153) give the same
  commands, statuses and bytes in Rust as in the functions compiled natively by
  Lean (`rust/notes/tests/request_differential.rs`). There, the body of each of the 380 accepted
  replies is what serde_json writes for the same value and is read back by `decode_reply`, and
  the fingerprint of each of the 265 commands without a body is the `Debug` form of the command.
  The Go and the Python table functions of the notes are generated and compiled, a
  Python test imports them and runs their `load` on a few rows, and no differential test runs
  them.
- **Where the JSON libraries differ.** The lists hold the texts on which serde_json,
  `encoding/json/jsontext` and `json` agree. A test of each language
  (`rust/leangage/tests/json_library.rs`, `go/leangage/json_library_test.go`,
  `python/test/test_json_library.py`) states what its library and conversion file do with the
  others:

  | Text | Rust (serde_json) | Go (`encoding/json/jsontext`) | Python (`json`) |
  |---|---|---|---|
  | a `\u` escape of a surrogate outside a pair (`"\ud800"`) | refused | read as U+FFFD | refused: the conversion refuses a string without a UTF-8 encoding |
  | arrays in arrays | read to depth 127, refused from 128 | read to depth 10,000, refused from 10,001 | read at depth 2,000, refused at 200,000 (`RecursionError`; about 51,900 on the build tested) |
  | a number outside the range of a double (`1e400`) | refused | a number that is no `UInt64` | a number that is no `UInt64` |

  A refused text is answered 400 `body is not JSON`. A deep text that is read is answered 400
  with the kernel's message (`not a calculator command`), and a body with a lone surrogate that
  Go reads is a string holding U+FFFD. The 3 agree on the rest of the tests' tables: `NaN`,
  `Infinity`, `01`, trailing data, a byte order mark, UTF-16, bytes that are not UTF-8 (Go's
  conversion checks `utf8.Valid` before the decoder), a control character in a string, an empty
  body and one of space only are refused; a member twice is handed over twice, and `decode`
  refuses the object; a member name in upper case stays as written, so `{"CMD":"get"}` is answered
  ``missing field `cmd` ``.
- **The request path calls the generated functions.** `tools/check-handlers.py` reads the 10
  files of the request path, the handler and the token module of each server library, the
  calculator's file that passes the calls on in each language and the notes' one in Rust, and
  fails when one lacks the call of a generated function (`authenticate`, `failed`, `request`,
  `respond`, `fingerprint`, `scope`, and `encode_reply` and `decode_reply` for the notes) or
  holds a JSON library, a status code (a constant of the HTTP library or a number from 100 to
  599) or the JSON writer. It reads the 3 conversion files, the one place of each language that
  calls the JSON library (`rust/leangage/src/json_text.rs`, 157 lines;
  `go/leangage/json_text.go`, 117 lines; `python/src/leangage/json_text.py`, 86 lines), and fails
  when one lacks the library's reading calls or holds a status code, a lookup of a member by its
  name, a comparison with a text or a type of the library that holds a whole value.
- **The servers give the answers of the generated functions.** `rust/calculator/tests/http.rs`,
  `python/test/test_http.py` and `go/calculator/http_test.go` send requests without a header,
  with another scheme, with a malformed, a forged and an expired token, with bodies that are not
  JSON, not UTF-8 or not a command, and with a reused idempotency key, and require the status
  and the body of each answer. A token that is both forged and expired is answered
  `bad token signature`. A body of nothing but `[`, 2 MiB of it in Rust and Go and 20,000 bytes
  in Python, is answered 400 `body is not JSON`, and one of as many `[` as `]` is answered 400: as no
  command where the library reads it (100 deep in Rust, 10,000 in Go and Python), as no JSON
  where it refuses the depth (500,000 in Rust, 10,001 in Go).
- **PostgreSQL stores and reads the rows as the model says.** The same 5,000 calculator commands
  run through the Rust PostgreSQL engine, on a server that the tests start in a temporary
  directory, give the same output as through the memory engine and as in Lean: once on an engine
  that remembers no snapshot, where every command reads the rows back, and once on one that
  remembers them; the notes commands and the Python and the Go engines run the same way, and the
  values below are read back by engines that remember no snapshot. Along the
  same commands, which mix 3 tenants, each command leaves every row but its own user's as it
  was (`rust/calculator/tests/postgres.rs`). Values of every kind, `NULL` included, at the bounds
  of 64 bits, text with quotes and characters outside ASCII and bytes 0 to 255, in a table and
  columns whose names hold `"`, read back as written; a text holding NUL, which PostgreSQL can't
  store, fails the command (`rust/leangage-pg/tests/values.rs`). A calculator server started
  again on the same database answers from the rows the first one stored. The same holds for the
  Python engine and the generated Python table functions behind it
  (`python/test/test_pg_calculator.py`, `python/test/test_pg_values.py`). There, tenants of 2^63
  and more are stored under the `Int64` with the same bits, and the 15 principals of the command
  list each run their commands from a thread of their own, with and without the advisory lock and
  the remembered snapshots, and get the replies Lean gives. The Rust and the Python calculator servers run on one database at
  once: the 5,000 commands go to them in turn and get the replies Lean gives, and a reply stored
  under an idempotency key by either server is replayed by the other and refused with another
  command. The same holds for the Go engine and the generated Go table functions behind it
  (`go/calculator/postgres_test.go`, `go/leangage/pg/values_test.go`, which reads the values
  back before and after a row is replaced, and stores empty bytes from a `nil` slice and from an
  empty one as empty bytes and not as `NULL`). The Rust and the Go calculator servers run on one
  database whose tables the Rust server's `LEANGAGE_LOCKDOWN` made: the 5,000 commands go to
  them in turn and get the replies Lean gives; every tenth carries an idempotency key and is sent
  again with that key to the other server, which answers alike (from the stored reply for the 424
  accepted ones) and refuses the key with another command; at the end both answer `get` alike for
  every user. No test runs the Python and the Go servers on one database. Each of the 3
  engines, in the test's process, shares a database with the Rust server in a process of its own:
  after each write of the server, the engine's next command, read-only or not, reads the value it
  wrote, and after 200 additions from the engine and 200 from the server at once, both read the sum
  (`engine_reads_what_a_server_process_wrote` in `rust/calculator/tests/postgres.rs`,
  `test_engine_reads_what_the_rust_server_wrote`, `TestEngineReadsWhatTheRustServerWrote`). The
  3,000 notes commands run through the Rust PostgreSQL engine give the same output
  as through the memory engine and as in Lean, listings and denials included
  (`rust/notes/tests/differential.rs`). Along them, which mix 2 tenants, each of the 1,826
  refused commands (1,383 denied by the guard) and of the 849 accepted read-only commands leaves
  every row of both tables as it was, and every other command leaves the other tenant's rows as
  they were (`rust/notes/tests/postgres.rs`). A body holding NUL is refused on both engines and
  writes no row. The stored form of each of the 1,174 replies of the list reads back as the reply,
  and a repeated keyed request gets the stored reply. A notes server started again on the same
  database answers from the rows the first one stored.
- **The PostgreSQL engines keep their contract.**
  [`rust/leangage-pg/tests/contract.rs`](../rust/leangage-pg/tests/contract.rs) runs a small
  kernel written in Rust through the Rust engine,
  [`python/test/test_pg_contract.py`](../python/test/test_pg_contract.py) one written in Python
  through the Python engine, and [`go/leangage/pg/contract_test.go`](../go/leangage/pg/contract_test.go)
  one written in Go through the Go engine, each with a hook the engine calls at 3 points of
  each attempt and a proxy that loses a COMMIT. Each Python test has the name of the Rust test
  with `test_` in front, and each Go test that name in camel case with `Test` in front
  (`TestSerializationFailuresRetryInANewTransaction`); each checks the same, except where the last
  2 columns say:

  | Item of the contract | Tests | Python | Go |
  |---|---|---|---|
  | 1. one attempt, one `SERIALIZABLE` transaction | `serialization_failures_retry_in_a_new_transaction` (3 attempts, each `serializable` and read-write, with distinct virtual transaction ids) | the same | the same |
  | 2. retries in a new transaction, at most 20 attempts | `serialization_failures_retry_in_a_new_transaction` (2 forced 40001s: each retry reads the outside commits), `serialization_failures_exhaust_after_max_attempts`, `deadlocks_are_retried` (a real 40P01 between the advisory lock and a row lock), `killed_before_commit_retries_once` (the backend terminated at each point, with and without a key: one effect, on a new connection; without a key, a backend terminated just before COMMIT gives `CommitUnknown` and no effect) | the same | the same |
  | 3. a refusal rolls back | `refusals_write_nothing` (no row, no stored reply; the key runs the command once it is accepted) | the same | the same |
  | 4. writes and reply commit together | `replies_commit_with_the_writes` (COMMIT lost before: neither; after: both), `idempotency_keys_replay_and_conflict`, `concurrent_requests_with_one_key_run_once` (32 clients, with and without the lock: one commit, 31 replays) | the same, with 32 threads | the same, with 32 goroutines |
  | 5. advisory lock before `BEGIN`, released before the pool | `advisory_lock_is_held_around_the_transaction` (a queued request waits before reading the table, then reads the first commit without a retry), `advisory_locks_are_released` (after a commit, a refusal, a terminated backend, a failed request and a caller that stopped waiting) | the caller that stops waiting is an HTTP client of `leangage.serve` that closes its connection while its request waits before COMMIT | the caller that stops waiting is an HTTP client of `RpcHandler` that closes its connection while its request waits before COMMIT |
  | 6. read-only commands | `read_only_path` (`SERIALIZABLE READ ONLY DEFERRABLE`, no advisory lock, retried after a terminated backend, a command that claims to read only and writes fails, a keyed read takes the write path) | the same | the same |
  | 7. COMMIT lost without a key | `lost_commit_without_key_is_unknown` (`CommitUnknown`, not retried; one case committed, one didn't), `lost_commit_with_key_runs_once` | first 10 commands on the proxy's one connection, more than the 5 after which psycopg prepares a statement it runs again, so the engine's COMMIT is still a simple query the proxy sees | the same |
  | 8. the version row and the remembered snapshot | `other_engines_writes_are_read` (another engine's write is read on the read-only, the write and the keyed path; the engine's own commits read no row), `lost_commit_forgets_the_snapshot` (after a COMMIT lost before and after the server ran it, the next attempt reads the rows, and then reads another engine's commit), `refusals_and_rollbacks_keep_the_snapshot` (a refusal, with and without a key, reads no row and leaves the value; after a backend terminated before COMMIT, without a key and retried with a key, the command runs on the committed rows), `remembers_at_most_cache_tenants` (2 tenants, the one used least recently forgotten; none with 0), `version_rows_conflict` (2 transactions that read a version and advance it: the second waits, then fails with 40001, with and without the row) | the same; the first 10 commands of `test_lost_commit_forgets_the_snapshot` go to another tenant, as in item 7 | the same |
  | with `SERIALIZABLE`, commits are serial | `concurrent_moves_are_serial` (64 clients, 512 moves between 4 cells, with and without the lock: every cell holds what the accepted moves left), `concurrent_engines_are_serial` (the same with 2 engines of 32 clients each, every move followed by a read: both engines then read what the cells hold) | the same, with 64 threads | the same, with 64 goroutines |
  | the roles | `roles_keep_the_engine_to_rows` (the tables belong to a role that can't log in; the engine's role can't alter, drop or truncate them; a superuser is refused as the engine's role) | the same | the same |

  A caller that stops waiting (a closed HTTP connection) doesn't cancel its command: the Rust
  engine runs the request in a task of its own to its end, the Python engine runs it on the thread
  of the HTTP request, which a closed connection doesn't stop, and the Go engine's `Execute` takes
  no context and runs on the goroutine of the HTTP request to its end. Its advisory lock is
  released, and it may commit. Not tested: a restart of the database server while clients write,
  a crash of the host, network delays short of a closed connection, and a full table of
  serializable conflicts (53200), which the engines retry. The Rust engine connects without TLS;
  the Python and the Go engines use TLS as the connection string's `sslmode` says (the default of
  libpq and of pgx is `prefer`).
- **The Rust notes server answers the guard's refusals with 403.** `rust/notes/tests/http.rs`
  sends denied writes, a read of a note the caller may not see (404), a bad body (422) and a
  command with another member (400).
- **The code that runs is generated from the proved source.** The build regenerates the 3
  targets and fails on a difference from the committed files.
- **No extra axioms.** Every theorem depends only on `propext`, `Classical.choice` and
  `Quot.sound`.

## Trusted

Trusted, with no theorem. What the Rust, Python and Go servers do around the generated functions
is written by hand, and every row holds for each of them:

| | Trusted |
|---|---|
| Translation | leanfran's Rust, Python and Go backends and their runtimes, rustc, CPython, the Go compiler, Lean's kernel |
| Engine | the memory engine: one command at a time per process, under one lock (Rust, Python), or per tenant, under the tenant's lock and in its `leanfran.Region` (Go); replies stored per idempotency key. The PostgreSQL engines: the 8 items of their contract, PostgreSQL's `SERIALIZABLE` (its commits equal a serial order) and its deferrable read-only snapshot, the conversion of values to parameters and of columns back to values, the stored form of the calculator's replies (`Storage::encode_reply` and `decode_reply`, `Storage.encode_reply`: 8 bytes), and for the notes the reading of the bytes of a stored reply as UTF-8 before `decodeReply` gets the text, and that the engine's role isn't a superuser and doesn't own the tables. In Rust, tokio-postgres and deadpool-postgres, and each value a parameter of the type PostgreSQL inferred. In Python, psycopg and the libpq it bundles, the engine's pool, each value a parameter of the type of its kind, and that the generated Python computes what Lean computes when several threads call it at once, as the PostgreSQL engine does and the memory engine, under its lock, doesn't. In Go, pgx and pgxpool, which take the `PG*` environment variables as the defaults of the connection string, each value a parameter of the type PostgreSQL inferred, and that the generated Go computes what Lean computes when several goroutines call it at once, as the PostgreSQL engine does for its requests and the memory engine for different tenants, each in a `leanfran.Region` of its own |
| Authentication | HMAC-SHA256 and the constant-time comparison of tags, which each server computes over the payload `authenticate` returns; the secret and its storage; the system clock, whose time each server gives `request`; that a server answers a tag that does not match with `failed` of `badSignature`; the table of accepted headers (a header whose token was accepted once is recognised by its exact bytes and gets the claims read then, without a second reading; its expiry is checked by `request` on every request) |
| Wire format | that each handler turns the outcome of its engine into the argument of `respond` and `failed` as the names say (`rust/leangage/src/http.rs`, `python/src/leangage/http.py`, `go/leangage/http.go`) |
| JSON input | serde_json (Rust), `encoding/json/jsontext` (Go) and `json` (Python), and the conversion file of each server library (`rust/leangage/src/json_text.rs`, `go/leangage/json_text.go`, `python/src/leangage/json_text.py`): that the tokens handed to `request` and `decodeReply` are those of the text of the body and of the stored reply, in its order, with every member of an object, a number as the text of its token (in Rust, where serde_json reads the number, the decimal of a token that is a `u64` and a text with a sign or an exponent for every other number) and a string and a key as their text, packed in one text as `pack` packs them (the kinds, a line feed, and the texts of the numbers, the strings and the keys, each but the last after the count of its characters and a colon); for the text that spells a command `c`, `pack (lexemesOf c)`, and for the text `encodeReply` writes for a reply `r`, `pack ((replyToks r).map Lexeme.ofStrTok)`, the tokens it writes with a number as its decimal; that bytes that are no JSON text give no tokens. serde_json's `arbitrary_precision` feature stays off: with it a number reaches the conversion as an object with a private member name, which a body can spell too. What is proved starts at those tokens. The texts on which the 3 libraries differ are listed above |
| HTTP | axum, hyper and tokio (Rust); `http.server` (Python); `net/http` (Go); reading the `Authorization` and the `Idempotency-Key` header as text (a header with a byte outside visible ASCII counts as absent in Rust and Go); in Go, deciding whether the body is longer than 2 MiB or could not be read, before `request` gets it; in Rust, axum's own answer (413) to a body longer than 2 MiB, which no handler sees; in Python, that the server reads a body of any length; sending the status and the bytes a generated function returned, with `Content-Type: application/json` |
| Call site | that a server runs the notes' `transition`. `handle`, the kernel without the guard, is generated and public too, and the guard's theorems say nothing about a caller of `handle`. For the request path of the calculator and of the notes, `tools/check-handlers.py` checks the calls |
| SQL | that PostgreSQL reads the text as `lexName_quote`'s lexer reads a quoted name; that PostgreSQL, sent `render q` with its parameters, fails or does to the tables what `run` says, and that a `SELECT` returns the rows `selected` says in some order (`ORDER BY` isn't modeled); that values compare as Lean values do (text character by character, bytes byte by byte); that the tables were made by `create` of the same schema, since `CREATE TABLE IF NOT EXISTS` keeps a table of that name as it is; that no text holds NUL, which the model stores and PostgreSQL refuses (for the notes, `accepted_no_nul` proves it of every body an accepted command writes) |
| Storage | that the PostgreSQL engines do what `Storage.Stored` says: each creates `tables` in a database without them, runs each command on the snapshot `load` builds of the rows of the compiled `SELECT` of each table or on the snapshot it remembers, and runs the statements compiled from `writes` of the accepted write set for the principal's tenant (`Kernel.tenant`, as the `Int64` with the same bits). An engine runs a command on a snapshot it remembers only while the tenant's row of `leangage_version` holds the version the engine read when it remembered it, and `Stored.cached` takes the database then to be one that `Stored` relates to that snapshot: the version is the same only if no transaction wrote the tenant's rows since. That holds when every transaction that writes a tenant's rows advances the tenant's version in the same transaction, as the 3 engines do, the version only grows, and `SERIALIZABLE` lets no 2 transactions advance it from the same value. For a row that exists, PostgreSQL's documentation says that a transaction whose `UPDATE` finds the row updated by a concurrent transaction that committed is rolled back ([Repeatable Read](https://www.postgresql.org/docs/18/transaction-iso.html#XACT-REPEATABLE-READ), which `SERIALIZABLE` extends, failing with 40001: [Serializable](https://www.postgresql.org/docs/18/transaction-iso.html#XACT-SERIALIZABLE)); it says nothing of `INSERT … ON CONFLICT DO UPDATE` at these levels ([INSERT](https://www.postgresql.org/docs/18/sql-insert.html#SQL-ON-CONFLICT)), so that the upsert fails the same way, for a row that exists and for one a concurrent transaction inserted, rests on `version_rows_conflict`; a writer that doesn't advance it, such as an engine built before `leangage_version` or an edit of the rows by hand, and tables dropped and made again while an engine runs, leave a remembered snapshot standing for rows that are no longer there. The code that does it is `rust/leangage-pg/src/lib.rs`, `python/src/leangage/pg/__init__.py` and `go/leangage/pg/pg.go`, and the `Storage` of the calculator in Rust, in Python and in Go and of the notes in Rust, which delegate to the generated functions; the differential tests and the contract tests check it |
| Specification | that `specStep` and the statements above say what a calculator and the notes should do; that the write list a kernel gives `ReadOnlySound` (`fun w => w.toList` for the calculator) holds every write of its write set; that `Valid`, `Accepts`, `sqlOf`, `renderSpec`, `exec`, `view`, `Sel` and `Lists` say what the SQL compiler should do; that `TenantIsolation`, `Storage`, `Loaded` and `Stored` say what storing a kernel should mean; that the calculator's `lookup` and `enc` and the notes' `enc` and `encTable` say which rows a snapshot stands for, and that `SameRows` says when 2 snapshots differ only in the order of their rows; that `v1.<tenant>.<user>.<expiry>.<hex>` with the signature over the bytes before the last dot is the token a client should send; that `Value.print` and `printToks` print JSON as RFC 8259 defines it, and `lexStr` reads a string as RFC 8259 does for the escapes `write` uses; that `replyValue` and `errorValue` are the bodies a client should read; that `encodeCommand` is the spelling of a command a client should send, and that the statuses and messages of `Leangage.Http`, `Calculator.Wire` and `Notes.Wire` are the ones a client should get; that the grammar `read` is written to accept is that of RFC 8259 |
| Policy | that `permits`, `visible`, `stored`, `view`, `disclosed` and `readOnly` of the notes say who should see and change what: the guard enforces them as written |

The Python and Go notes kernels run only in the differential tests; only Rust has a notes server.
The Rust, the Python and the Go calculator servers and the Rust notes server have a PostgreSQL
engine; without `LEANGAGE_DATABASE_URL` a server keeps the state in its memory, where it is lost
on restart.
