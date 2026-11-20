# Borsuk documentation

Borsuk is a language for services of every size. Coding agents write it. People read it through tools.

## Design

| Document | Content |
|---|---|
| [Language core v0.1](design/language-core-v0.1.html) | The design of the language, version 0.1 (19 November 2026). Each release builds parts of this design. |
| [Verified FSM language](design/verified-fsm-language.md) | The first design note (18 November 2026). It gives the design principles and a review of other work. The language core design is newer. |

## Roadmap

| Document | Content |
|---|---|
| [Milestones](roadmap/milestones.md) | The milestones from v0.0.1 to v0.1.0, the implementation stack, and the reasons for the order. |

## Releases

### v0.0.1: core and interpreter

Status: released, tag `v0.0.1`.

| Document | Content |
|---|---|
| [Plan](releases/v0.0.1/plan.md) | The contract of v0.0.1: the core IR grammar, the semantics, the static rules, the proof, the corpus, the layout and `check.sh`. |
| [Goal](releases/v0.0.1/goal.md) | The instructions for the agent that built v0.0.1: the roles, the loop for each phase, the gates and the stop rules. |

## Code

| Path | Content |
|---|---|
| `spec/` | The Lean 4 reference. It builds the executable `brk-ref` and the proof `Borsuk.coverage`. |
| `crates/` | The Rust mirror of the reference. It builds the executable `brk`. |
| `corpus/` | The accepted, rejected and failing programs, with their expected output. |
| `check.sh` | The only gate. Run `./check.sh all` from the repository root. |
