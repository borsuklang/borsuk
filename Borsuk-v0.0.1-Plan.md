# Borsuk v0.0.1 work plan

The agent that builds v0.0.1 follows `Borsuk-v0.0.1-Goal.md`.
The sources are the design `Borsuk-Language-Core-v0.1.html` (sections 3, 4, 5, 10, 11, 16) and `Borsuk-Milestones.md`.

## 1. Result

v0.0.1 gives one executable semantics of the Borsuk core in Lean 4 (`borsuk-ref`, the reference) and one in Rust (`borsuk`). Their outputs on the corpus of section 6 are equal.

The grammar in section 2 is the complete language of v0.0.1.

## 2. Core IR

One file is one closed program.

- Items, variants, states, groups, commands and queries share one name space. The file declares each name in it one time.
- A local name is a parameter, a state field, a `let` name, a pattern binder or an actor. A record field name is outside the name space.
- `ID` = `[A-Za-z][A-Za-z0-9_]*`. A `SYM` has the same pattern as `ID`. It is outside the name space.
- Reserved words are each form head of the grammar, each built-in type name, `true`, `false`, `Fired`, `ConsoleOut` and `Timer`. A declared name is never a reserved word. A local name is never `true` or `false`.
- `INT` = `0` or `-?[1-9][0-9]*`, in the signed 64-bit range. `TEXT` = `"..."` with the escapes `\"` and `\\` only. A code point below U+0020, or U+007F, in a `TEXT` is a `parse` error. An `INT` out of range is a `parse` error.
- Space, tab, newline and parentheses split tokens. The grammar has no comment form.
- In the grammar, `X?` means zero or one `X`.

```
program ::= (program item*)
item    ::= (newtype ID type)
          | (record ID (ID type)+)
          | (enum ID (ID type*)+)
          | (role ID)
          | (fn ID ((ID type)*) type (uses ConsoleOut?) block)
          | (protocol ID msg+)
          | (machine ID (key type) (protocol ID) (uses ConsoleOut? Timer?) (init ID) state+ group* in+)
          | (deployment ID (platform cli) (entry ID))
          | (example ID (machine ID) (key xexpr) actor* line+)
msg     ::= (command ID ((ID type)*) type (rejects SYM*))
          | (command ID ((ID type)*) type (rejects SYM*) (by ID))
          | (query ID ((ID type)*) type)
state   ::= (state ID (ID type)*)
group   ::= (group ID ID+)
in      ::= (in ID cell+)
cell    ::= (on ID block)
block   ::= (block stmt* tail)
stmt    ::= (let ID expr) | (do expr)
tail    ::= (value expr)
          | (next (ID expr*)) | (next (ID expr*) (outcome expr))
          | (stay) | (stay (outcome expr))
          | (reject SYM) | (answer expr) | (ignore stale) | (impossible)
          | (match expr (arm pat block)+)
expr    ::= INT | TEXT | true | false | (unit) | (dur INT) | ID
          | (env now) | (env step) | (env sender) | (env deadline)
          | (call ID expr*) | (new ID expr*) | (get expr ID)
          | (some expr) | (none) | (ok expr) | (err expr)
          | (+ expr expr) | (- expr expr) | (* expr expr)
          | (== expr expr) | (< expr expr) | (and expr expr) | (not expr)
          | (ConsoleOut.print expr) | (Timer.after expr) | (Timer.cancel expr)
pat     ::= true | false | (none) | (some bind) | (ok bind) | (err bind) | (ID bind*)
bind    ::= _ | ID
type    ::= Unit | Bool | Int | Text | Time | Duration | Principal | StepId | Ticket
          | (Option type) | (Result type type) | ID
actor   ::= (actor ID ID*)                              name, then roles
line    ::= (send ID ID xexpr* (expect fact*))          actor, command or query, arguments
          | (fire xexpr (expect fact*))
fact    ::= (outcome xexpr) | (reject SYM) | (answer xexpr) | (refused forbidden)
          | (fault SYM) | (ignored) | (state ID xexpr*)
xexpr   ::= INT | TEXT | true | false | (unit) | (dur INT) | ID
          | (new ID xexpr*) | (some xexpr) | (none) | (ok xexpr) | (err xexpr)
          | (step INT) | (ticket INT)
```

Names and types:

- `(in S ...)` binds the fields of state `S` by their declared names. `(in G ...)` for a group binds no name.
- `(on I ...)` binds the parameters of input `I` by their declared names. `Fired` binds `ticket`.
- The inputs of a machine are the messages of its protocol, and `Fired` when its `uses` holds `Timer`.
- `(new T e*)` takes the record fields or the variant fields in declared order. A newtype has one constructor. `(new T e)` builds it, and the pattern `(T x)` opens it. A variant with no field is `(new Red)`, and its pattern is `(Red)`. `(get e F)` works on records only.
- An operation is `ConsoleOut.print` (`Text` to `Unit`), `Timer.after` (`Duration` to `Ticket`), `Timer.cancel` (`Ticket` to `Unit`), or a `call` of a `fn` with `(uses ConsoleOut)`.
- `(none)`, `(ok e)` and `(err e)` take their type from their position. The right side of `let`, the body of `do`, a `match` subject and the left side of `==` give no type. These forms are a `type-mismatch` there.
- The expression of an `outcome` fact has the result type of the command. The expression of an `answer` fact has the result type of the query.
- `==` works on each type. `<` works on `Int`, `Time` and `Duration`. `+`, `-` and `*` work on `Int`. `and` and `not` work on `Bool`.
- A `match` subject has the type `Bool`, `Option`, `Result`, an enum or a newtype.
- In an example, an actor name is the `Principal` with that name. `(step N)` is the `StepId` with sequence `N`. `(ticket N)` is the ticket with sequence `N` and index 0.

This is the `Confirm` cell of the `Held` block of the Slot machine in this form.

```
(in Held
  (on Confirm
    (block
      (match (and (== hold token) (== holder (env sender)))
        (arm false (block (reject NotHeld)))
        (arm true (block
          (do (Timer.cancel timer))
          (next (Booked holder hold) (outcome (unit)))))))))
```

## 3. Semantics

| Topic | Rule |
|---|---|
| Int | Signed 64 bits. `+`, `-` and `*` with an overflow give the fault `overflow`. Lean uses `Int` with a range check after each operation. Rust uses `i64::checked_*`. |
| Text | Valid UTF-8. Equality compares bytes. Lean reads a file with `IO.FS.readBinFile` and `String.fromUTF8?`. |
| Time, Duration | Signed 64-bit nanoseconds. `(dur N)` is `N` nanoseconds. `Time` has no literal. |
| Envelope | `(env now)` and `(env deadline)` are `Time`. `(env step)` is `StepId`. `(env sender)` is `Principal`. The runtime does not act on the deadline in v0.0.1. |
| Principal | A name. Two principals are equal when their names are equal. Roles are not part of the value. |
| Order | Arguments evaluate left to right. `and` evaluates both sides. Statements run in order. Outputs keep statement order. |
| Step | A step is a function of (state, envelope) to (next state, outputs, result), or to a fault. |
| Fault | The state does not change. The runtime drops the outputs. The result is `(fault F)`. `F` is the fault kind, `overflow` or `impossible`. The runtime stores the sequence number of a fault step. The next step takes the next number. |
| `impossible` | A cell that reaches `impossible` gives the fault `impossible`. |
| Instance | An example has one instance. The runtime keeps its (sequence, state). Before the first step, the state is the `init` state and the sequence is 0. The life number is 1 in v0.0.1. |
| Sequence | Each step takes the stored sequence plus 1, and the runtime stores that number. The first step has the number 1. A query is not a step and takes no number. |
| `stay`, `reject`, `ignore stale` | The state does not change. `ignore stale` has no output, and its result is `(ignored)`. |
| `Timer.after d` | It is an output. It gives `(ticket M K 1 seq idx)` at once. `idx` counts the tickets that the step made before it. |
| `Timer.cancel t` | It is an output. The runtime keeps no timer set in v0.0.1. |
| `fire` | `fire` runs the input `Fired(ticket)` on the instance of the example, with the sender `(principal "runtime")`. |
| Admission | A command with `(by R)` from a sender without the role `R` gets `(refused forbidden)`. No step runs, and the instance does not change. |
| Example | Each example starts with an empty runtime. In each envelope, `now` and `deadline` are `(time 0)`. |
| Facts | Each fact of a line must hold. `(state ...)` compares with the state after the line. Each other fact compares with the result of the line. |
| `main` | `run` prints the text of each `ConsoleOut.print` of the entry `fn` and a newline, in order. |

Traces and messages use the canonical value text.

| Value | Text |
|---|---|
| Int, Bool, Unit | `42`, `-3`, `true`, `(unit)` |
| Text | `"..."`. `"` prints as `\"`, and `\` prints as `\\`. |
| Duration, Time | `(dur N)`, `(time N)`, in nanoseconds |
| Principal | `(principal "a")` |
| StepId, Ticket | `(step M K life seq)`, `(ticket M K life seq idx)` |
| Records, enums, newtypes | `(Name v*)`. `Name` is the record name, the variant name or the newtype name. |
| Option, Result | `(some v)`, `(none)`, `(ok v)`, `(err v)` |

`test` prints one trace line for each event, in the order of the events.

```
(step (step M K life seq) (now T) (deadline T) (by P) (input (I v*)) (result R) (state (S v*)) (outputs O*))
(query (M K) (now T) (deadline T) (by P) (input (I v*)) (result R))
(refused (M K) (now T) (deadline T) (by P) (input (I v*)) forbidden)
R ::= (outcome v) | (reject SYM) | (answer v) | (ignored) | (fault F) | (next)
O ::= (ConsoleOut.print v) | (Timer.after d ticket) | (Timer.cancel ticket)
```

The result `(next)` marks a `Fired` step that ends in `next` or `stay`. In the templates, `M` is the machine name. `life`, `seq` and `idx` are decimal numbers. `K`, `T`, `P`, `d`, `ticket` and `v` are canonical value texts. One space separates two elements of a form, and no other space exists. Each output line ends with one U+000A. Each output goes to stdout, except the usage line.

## 4. Static rules

`check` runs the rules in table order and stops at the first code that has an error. It prints one line, `error[CODE]: MESSAGE`, for the first error in tree order. Tree order is items in file order, then depth first, left to right. For `missing-cell`, `check` prints one line for each missing cell. The order is states in declared order, then inputs in protocol order, with `Fired` last. For `duplicate-cell`, `check` uses the same order. It prints one line, for the first pair that has two cells. An error with two places has the position of the second place. `check` also examines each example. ITEM is the `fn`, machine or example that contains the error.

| Code | The checker refuses | Message |
|---|---|---|
| `parse` | Text that is not a valid S-expression, invalid UTF-8, a form that is not in the grammar, a reserved word as a declared name, or `true` or `false` as a local name | ``text is not a program`` |
| `unknown-name` | A name with no declaration of the kind that its position needs. An input that the machine does not have, a state of a different machine, `Fired` on a `send` line, and `Fired` on a `fire` line for a machine without `Timer` are such names. | ``name `N` is not declared`` |
| `duplicate-name` | A name declared twice, a local name that equals a declared name or a local name in scope, or two names in one list of record fields, state fields or parameters | ``name `N` is declared twice`` |
| `recursion` | A `fn` body that calls a `fn` that the file declares after it, or the `fn` itself | `` `F` calls `G` before its declaration`` |
| `wrong-ending` | A tail that the context does not permit (table below), or an operation on a path that ends in `reject`, `answer`, `ignore stale` or `impossible` | ``wrong ending in `ITEM` `` |
| `type-mismatch` | A type that differs from the type its position needs, a wrong number of arguments, a `get` of a field that the record does not have, a pattern of a type that differs from the subject type, an `outcome` fact on a line that is not a `send` of a command, or an `answer` fact on a line that is not a `send` of a query | ``type mismatch in `ITEM` `` |
| `match-arms` | A `match` whose arms do not have each constructor of the subject type exactly one time | ``match in `ITEM` does not name each constructor once`` |
| `effect-position` | An operation that is not the whole right side of `let` or the body of `do`, or a `do` without an operation | ``wrong operation position in `ITEM` `` |
| `effect-not-declared` | An operation whose effect is not in `uses` | `` `ITEM` does not declare effect `E` `` |
| `env-position` | `(env ...)` in a `fn`, or `(env step)` in a query cell | `` `(env X)` is not legal in `ITEM` `` |
| `init-has-fields` | An `init` state with fields | ``init state `S` of machine `M` has fields`` |
| `duplicate-cell` | Two cells for one pair of state and input | ``machine `M` has two cells for (S, I)`` |
| `missing-cell` | A pair of state and input with no cell | ``machine `M` has no cell for (S, I)`` |
| `reject-not-declared` | A `reject` tail with a reason that is not in the `rejects` list of the command | ``command `C` does not declare reject `R` `` |
| `bad-entry` | A deployment entry `fn` that has parameters or a result other than `Unit`, or a second deployment | ``deployment `D` has no legal entry`` |

| Context | Permitted tails |
|---|---|
| `fn` | `value` |
| Command cell | `next` or `stay` with `outcome`, `reject`, `impossible` |
| Query cell | `answer`, `impossible` |
| `Fired` cell | `next` or `stay` without `outcome`, `ignore stale`, `impossible` |

A `match` tail is legal in each context. Each arm block follows the row of that context. A path is the statements, the `match` subjects and the tails from the start of a cell to one tail that is not a `match`. An operation at any depth in them is on the path. A message has no leading space and no trailing space.

## 5. Lean proof

`Eval` recurses structurally on the syntax tree. Only `call` uses fuel, one unit for each nested `call`. The start fuel is the number of `fn` items. `Eval` returns `stuck` when the fuel is 0. Rust has the same fuel. `stuck` cannot occur after `check`, because the `recursion` rule limits the depth of nested calls to the number of `fn` items.

`Borsuk.coverage` has the premise `check p = .ok ()`. Let `m` be a machine of `p`, `s` a state of `m` and `i` an input of `m`. Then the cell lookup that `step` calls finds a cell.

The proof has no `sorry` and no new `axiom`. Imports come only from Lean core (`Init`) and this package.

## 6. Corpus

```
corpus/accept/hello.sexp      + hello.out ("hello, world" and a newline)
corpus/accept/slot.sexp       + slot.trace
corpus/accept/tally.sexp      + tally.trace
corpus/reject/<code>.sexp     + <code>.err, one pair for each code in section 4
corpus/fail/wrong-fact.sexp   + wrong-fact.out
```

| File | Content |
|---|---|
| `slot.sexp` | The Slot machine of design section 5, with no durability name and no spec. The fields `holder` and `owner` and the answer of `Owner` use the type `Principal`. The file declares no `Client`. `HoldToken` is `(newtype HoldToken StepId)`. `SlotId` is `(newtype SlotId Int)`. Each example uses the key `(new SlotId 7)`. Three examples: (1) `old_timer_keeps_second_hold` from the design, with the same meaning. (2) `Create` by an admin, then `Hold`, then `Confirm` by the holder gives `(outcome (unit))` and the state `Booked`, then a second `Confirm` by the holder gives `(outcome (unit))`. (3) `Create` from a non-admin gives `(refused forbidden)`, `Hold` on an absent slot gives `(reject NoSlot)`, the query `Owner` gives `(answer (none))`, and `fire` in `Absent` gives `(fault impossible)`. |
| `tally.sexp` | It has records, enums, newtypes, `Option`, `Result`, pure calls and a call of a `fn` with `(uses ConsoleOut)`, `ConsoleOut` in a machine, each operator, `(env now)`, `(env deadline)` and the fault `overflow`. |
| `reject/missing-cell` | The Slot machine with the command `Release` added to the protocol and no cell for it. The `.err` file holds the four lines of the design with the same text. |
| `reject/<code>` | Each file gives exactly its own code. |
| `fail/wrong-fact` | One example with one false fact. The `.out` file holds the expected output. |

Each tail, fact and trace line kind runs in at least one example. Each other alternative of each grammar rule appears in at least one accepted file. A `.trace` file holds the stdout of `borsuk-ref test FILE`. The coordinator selects each name and each value that this section does not give.

## 7. Layout and `check.sh`

```
rust-toolchain.toml              channel 1.98.1
Cargo.toml, Cargo.lock           workspace
.gitignore                       target/ and spec/.lake/
crates/borsuk-core/              Cargo.toml; src/ lib.rs ir.rs read.rs check.rs eval.rs runtime.rs print.rs
crates/borsuk-cli/               Cargo.toml; src/main.rs: the executable `borsuk` and the example runner
spec/                            lean-toolchain, lakefile.toml, lake-manifest.json, Borsuk.lean
spec/Borsuk/                     Ir Read Check Eval Runtime Print .lean
spec/Borsuk/Proofs/              Coverage Axioms .lean
spec/Main.lean                   the executable `borsuk-ref` and the example runner
corpus/                          section 6
check.sh
```

The paths of the executables are `target/release/borsuk` and `spec/.lake/build/bin/borsuk-ref`.

| Use | Behavior |
|---|---|
| Each command | Runs `check` first. With an error, it prints the error line or lines and exits 1. |
| `check FILE` | No output, exit 0. |
| `run FILE` | Prints the lines, exit 0. A fault prints no `ConsoleOut` line, prints `fault F` and exits 1. With no deployment, it prints `error[bad-entry]: no deployment` and exits 1. |
| `test FILE` | For each example in file order, it prints the trace lines of the example lines that ran, then `pass NAME` or `fail NAME: line N`. An example stops at its first failed line. N counts the `line` forms of the example from 1. Exit 0 when all examples pass, else 1. With no example, no output and exit 0. |
| An unreadable file | `error[parse]: text is not a program`, exit 1. |
| Any other use | The usage line below, on stderr, exit 2. NAME is `borsuk` or `borsuk-ref`. |

```
usage: NAME check|run|test FILE
```

`check.sh STAGE` runs the steps of its stage and stops at the first failed step.

| Step | Check |
|---|---|
| 1 | `cargo fmt --check`, `cargo clippy --workspace --all-targets -- -D warnings`, `cargo build --release` |
| 2 | `cd spec && lake build --wfail` |
| 3 | `cd spec && lake env lean Borsuk/Proofs/Axioms.lean` prints the axiom line of `Borsuk.coverage`. Each axiom in it is `propext`, `Classical.choice` or `Quot.sound`. |
| 4 | The comment search below finds nothing. |
| 5 | Each accepted file: `check` exits 0 with no output. `test` output equals `<name>.trace`, exit 0. `hello.sexp` has no example and no trace file. `run hello.sexp` output equals `hello.out`, exit 0. `run slot.sexp` output equals `error[bad-entry]: no deployment`, exit 1. |
| 6 | Each reject file: `check` output equals `<code>.err`, exit 1. |
| 7 | The fail file: `test` output equals `wrong-fact.out`, exit 1. |

| Stage | Steps |
|---|---|
| `setup` | 1, 2, 4 |
| `lean` | `setup`, 3, and 5 to 7 for `borsuk-ref` |
| `all` | Steps 1 to 4, and 5 to 7 for both executables |

This is the comment search of step 4.

```
grep -rnE '^[[:space:]]*(//|/\*|--|/-)|[[:space:]](//|--)[[:space:]]' crates spec --include='*.rs' --include='*.lean'
```

## 8. Phases

| Phase | Work | Done when |
|---|---|---|
| P0 Setup | Branch `build/v0.0.1`. Install `elan` with the command below. Pin the newest release tag of `leanprover/lean4` with no `-rc` suffix. Write the tag in the message of the P0 commit. Pin Rust 1.98.1. Crate and package skeletons, `.gitignore`, `check.sh`. | `check.sh setup` passes. |
| P1 Corpus | Each corpus file except the `.trace` files. | Gate G1 passes. In G1, a Fable reviewer examines the meaning of each file against the grammar, the design and this plan. |
| P2 Lean | `Ir`, `Read`, `Check`, `Eval`, `Runtime`, `Print`, `Main` and the proof. The coordinator corrects a corpus file only where the file breaks this plan, and writes each correction in the commit message. When `Main` builds, the coordinator makes the `.trace` files with `borsuk-ref test FILE`. The coordinator makes them again each time a file in `spec/` changes. | `check.sh lean` passes. Gate G2 passes. In G2, a Fable reviewer examines each line of `slot.trace` and `tally.trace` against sections 2 and 3. The coordinator then freezes the corpus and the traces. |
| P3 Rust | The two crates. | `check.sh all` passes. |
| P4 Release | Gate G3. In G3, a Fable reviewer examines the full diff against this plan and the design. Then merge to `main` with `git merge --ff-only`. Run `check.sh all` on `main`. Make the tag `v0.0.1`. Push `main` and the tag. | The tag is on the remote. |

This is the `elan` install command of P0.

```
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
```

## 9. Rules

Build:

- Do not build a part of a later milestone. Do not add a hook, a trait, a generic parameter or a setting that only a later milestone needs.
- The five rules of design section 16 are the only boundaries for later milestones. In v0.0.1, the platform is a value in the deployment. The runtime core starts no thread, opens no file, reads no clock and knows no platform. The `cli` host does all I/O. No value or index in the IR depends on the pointer size.
- Each concept has one type. The IR types are the syntax tree, and no second tree exists in Lean or in Rust.
- Lean is the reference. Rust uses the module names and the function names of Lean in `snake_case`, and the same rule codes.
- Do not use external code. Rust uses `std` only. Each crate has `#![forbid(unsafe_code)]`.
- Do not use a `HashMap`, or any order that is not stable, to make an output.
- Do not do performance work.

Tests:

- The corpus, `check.sh` and the proof are the only checks. Do not write a unit test, a test helper or a mock.
- A frozen file does not change. The frozen files are the corpus and the traces.

Text:

- Code has no comments and no doc comments.
