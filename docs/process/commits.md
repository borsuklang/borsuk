# Commit messages

Each commit message obeys [Conventional Commits 1.0.0](https://www.conventionalcommits.org/en/v1.0.0/). The tool [cocogitto](https://docs.cocogitto.io/) (`cog`) checks the rule. Its configuration is `cog.toml` in the repository root.

## Form

```
type(scope): description

Body in ASD-STE100 Simplified Technical English.

Co-Authored-By: ...
```

| Part | Rule |
|---|---|
| `type` | One type from the table below. |
| `(scope)` | Optional. One scope from the table below. `cog` refuses other scopes. |
| `!` | Put `!` before the colon when the change breaks a published behavior, for example `feat(cli)!: ...`. |
| `description` | An imperative verb first, for example "add", "remove", "correct". |
| Body | Optional. It tells what changed and why. |

`cog` accepts merge commits and `fixup!`, `squash!` and `amend!` commits.

## Types

| Type | Use it for |
|---|---|
| `feat` | A new part of the language, the checker, the runtime or the CLI. |
| `fix` | A correction of wrong behavior. |
| `docs` | A change in `docs/` only. |
| `style` | A change of format only, for example `cargo fmt`. |
| `refactor` | A change of the code shape that keeps the behavior. |
| `perf` | A change for speed or memory that keeps the behavior. |
| `test` | A change in `corpus/`. |
| `build` | A change of the toolchain, Cargo, Lake or the Git setup. |
| `ci` | A change of `check.sh`. |
| `chore` | Other work that changes no behavior. |
| `revert` | A commit that reverts an earlier commit. |

## Scopes

A Lean module and its Rust mirror share one scope.

| Scope | Paths |
|---|---|
| `ir` | `spec/Borsuk/Ir.lean`, `crates/borsuk-core/src/ir.rs` |
| `read` | `spec/Borsuk/Read.lean`, `crates/borsuk-core/src/read.rs` |
| `check` | `spec/Borsuk/Check.lean`, `crates/borsuk-core/src/check.rs` |
| `eval` | `spec/Borsuk/Eval.lean`, `crates/borsuk-core/src/eval.rs` |
| `runtime` | `spec/Borsuk/Runtime.lean`, `crates/borsuk-core/src/runtime.rs` |
| `print` | `spec/Borsuk/Print.lean`, `crates/borsuk-core/src/print.rs` |
| `float` | `spec/Borsuk/Float.lean`, `crates/borsuk-core/src/float.rs` |
| `approx` | `spec/Borsuk/Approx.lean`, `crates/borsuk-core/src/approx.rs` |
| `math` | `spec/Borsuk/Math.lean`, `crates/borsuk-core/src/math.rs` |
| `decimal` | `spec/Borsuk/Decimal.lean`, `crates/borsuk-core/src/decimal.rs` |
| `codec` | `spec/Borsuk/Codec.lean`, `crates/borsuk-core/src/codec.rs` |
| `cli` | `spec/Main.lean`, `crates/borsuk-cli/` |
| `proof` | `spec/Borsuk/Proofs/` |
| `corpus` | `corpus/` |
| `toolchain` | `rust-toolchain.toml`, `Cargo.toml`, `spec/lean-toolchain`, `spec/lakefile.toml` |
| `git` | `cog.toml`, `.gitignore` |
| `experiment` | `experiments/` |
| `design`, `roadmap`, `release`, `process` | The matching folder in `docs/` |

To add a scope, add it to `scopes` in `cog.toml` and to this table.

## Examples

```
feat(check): add the duplicate-cell rule
fix(eval): keep the outputs of a fault step empty
test(corpus): add a reject file for wrong-ending
docs(release): record the owner's decision on actor scope
build(git): add the cocogitto configuration
```

## Setup after a clone

1. Install `cog` 7.0.0 or later. Use a release binary from GitHub (`cocogitto/cocogitto`) or `cargo install --locked cocogitto`.
2. Install the hook from `cog.toml` one time in each clone:

```
cog install-hook --all
```

The `commit-msg` hook then runs `cog verify` on each new commit. Do not use `git commit --no-verify`.

## Commands

| Command | Result |
|---|---|
| `cog check` | Checks each commit after the newest tag. The commits up to `v0.0.1` use an older form, so `cog check` does not examine them. |
| `cog verify "feat(check): add the rule"` | Checks one message. |
| `cog log` | Shows the history by type and scope. |
| `cog changelog` | Prints a changelog from the commits. |
