# Author checklist

Apply each item before round 1. Each item comes from a defect that a reviewer found in the v0.0.2 plan. The example after each item is that defect.

## Scope (NOT-PLANNED)

- For each item, form, keyword, operation, conversion, type, rule, error code, fault, theorem, harness, file, mode, tool and library, name the text that asks for it: the milestone row, its exit gate, a design sentence or an owner decision. Else it must be the smallest means to build, test or prove such an item. Remove each other item. Example: a new `cases` test form, conversions, `neg` and `abs`, three extra theorems, two extra Kani harnesses, a search of 2^20 inputs and the MPC library were all removed.
- Prefer a form of an earlier release to a new form. Example: an `example` with a query and an `answer` fact replaced a new `cases` item.
- Make a rule that the grammar can state a grammar rule, not a new error code. Example: `(record ID field+ ifield*)` replaced the code `field-init-order`.
- Reserve only form heads and type names. Example: rounding-mode words have a fixed position and need no reservation.
- Remove each source that no section uses.

## One canonical form

- Remove an operation that another form gives with the same bits. Example: `neg` equals `(- (f64 -0) x)`.
- Fix a parameter that has no effect to one value. Example: a `round` that cannot lose a digit must use the mode `exact`.

## Earlier rules and the design

- The table of changes (plan section 1.1) lists each change to a rule of an earlier plan, by section: the grammar, the types, the faults, the codes and their order, the tree order of errors, ITEM, the `test` output, the steps of `check.sh`, "the only checks", "no external code", "no performance work" and the mirror rule.
- Each difference from the design is named in the plan at its place, with its reason.
- Each rule of the goal that the plan needs an exception to is one of the exceptions that the goal permits (host rules, freeze points, mirror rule).

## Owner decisions

Ask about each of these kinds before round 1, with a recommended option.

- The equality and the order of each new type.
- The text form of each new literal and value, and whether only that text is legal.
- The set of library functions or operations.
- The model of a new numeric type, its operations and its conversions.
- Whether a theorem takes its strict form (no fuel loophole, totality).
- The tool and the language of each oracle and each independent check.
- For an experiment: the value table and its sources, the kind of mean, the form of each runtime header (the same in each candidate, or the form of each candidate), the form of each version field, what each candidate keeps in memory, what a decision rule does when a candidate fails only one rule, and each limit that costs check time.

## Exact semantics

- Give each text algorithm with its tie rules over all candidates. Example: the shortest float text compares candidates with a different exponent `n` too.
- Limit the length of each atom before any arithmetic, also the digits of an exponent. Example: `1e9999999999999999999999` would fill the memory.
- Put each table of special cases in the plan. Do not write "follow standard X". State what `<` and `>` mean for ±0 and ±∞ in the table.
- Give the order of two faults that one operation can meet.
- Give each threshold exactly. Example: the overflow threshold of IEEE 754 section 4.3.1.
- For each loop: why it ends, what a step does when it cannot reach its target, and its fault after the last step.
- Keep exact values small: an odd integer and an exponent, with a range test before a large integer.

## Bytes

- State the byte order, the bit order, the first index (tag 0, field 0, byte 0, bit 0), the width of each integer, the rule for each offset, the padding and each size limit.
- Give each variable part whose type depends on earlier bytes a length. Example: two different `StepId` values had the same bytes.
- Make no value depend on the pointer size: give each length and count a range.
- Give each old form (fewer fields) its exact layout.

## Proofs

- State each theorem with all premises. A premise such as "`encode` gives `some b`" must not make the theorem empty.
- When the exit gate says "inverse", also prove that encode succeeds for each typed value below the size limit.
- Define each predicate and each helper function in the plan (for example `Typed`, `full`, `size`), and require that each type name is declared.
- Say which functions use fuel, the start fuel, and that the proof shows it is sufficient.
- Permit `partial` only where a plan names it. Forbid `unsafe`, `@[implemented_by]` and `@[extern]`.

## Kani

- Match the real output: `VERIFICATION:- SUCCESSFUL` one time, and a line that ends with `** N of N cover properties satisfied` (the line starts with a space).
- Give each harness one `kani::cover!` for each type, and let `check.sh` hold the exact N of each harness. Do not refuse `UNREACHABLE`: Kani reports normal reach checks with it.
- Choose bounds that admit at least one accepted case of each type.
- Run each harness as `systemd-run --user --scope -q -p MemoryMax=2G -p MemorySwapMax=0 timeout -k 10 900 nice -n 19 ionice -c3 cargo kani -p CRATE --harness NAME`.
- P0 installs the toolchain of Kani with rustup if it is absent, and runs `cargo kani --only-codegen`.
- Declare `cfg(kani)` with `unexpected_cfgs` and `check-cfg` in the workspace lints. A package with its own `[workspace]` table has no `[lints]` table.

## Measurements and experiments

Most v0.0.2 findings were here.

- Source each row of a value table, show each derivation, and let the owner approve the table.
- Specify the generator completely: the algorithm with its constants, the seed, the draw order, the map from one draw to each kind (weighted choice, inclusive and exclusive ranges, characters, NaN patterns, operands in order).
- Give each candidate the same work, except the property under test. State its memory form, what each step reads, writes and copies, the write order (log record before the state change), and the buffers. No allocator call in a timed step. Pass each result to `black_box`.
- Treat runtime headers (identifiers, versions) by an owner decision: the same form in each candidate, or the form of each candidate.
- Specify the timing: the clock reads for each block, the warm-up time, the passes, the runs, the rotation formula, the repeat rule, which runs count, the CSV columns and file names.
- Give a formula for each number of the report, the t quantile for each degree of freedom, and the kind of mean.
- Make the decision table complete and ordered. Name each stop in it.
- Define the quiet host as a test with a wait limit, and say what happens when the bytes alone decide.
- Freeze the experiment code before the first timed run. Give it a smoke mode that runs each code path and prints no number.
- Let a gate compute each number again with its own program: the byte means, the ratios, the intervals and the decision. Compare the candidates with each other on each step, and give each candidate one refused input for each refusal.

## Corpus and oracle

- Write the oracle in the language that the owner chose (v0.0.2: Rust with `rug` and MPFR). Pin its version and its features, and build no library that it does not use.
- Let a gate run the oracle again and compare each file byte by byte with the working tree.
- Give each refused corpus item one cause, and make it differ from a valid item only in the bytes of that cause.
- Pin each external data source by URL and tag. Test each hard case after the copy.
- Let a program write each large file (thousands of fields or variants).
- Put each grammar alternative into an accepted file, and give each new error path a reject file.
- Specify each random corpus draw as in the experiment.

## Process and gates

- A gate runs before the commit of its phase. Compare with the working tree, not with a commit.
- `check.sh` is code: a phase that changes it has a phase review. After P0, `check.sh` changes only toward the plan.
- At most two heavy jobs run at the same time, and the coordinator counts. Run `check.sh` with `CARGO_BUILD_JOBS=2 LEAN_NUM_THREADS=2 nice -n 19 ionice -c3`.
- Give each phase that must commit two times its own row (v0.0.2: P1a code, P1b run).
- Give each gate of a computed byte string or number a program, not a computation by hand.
