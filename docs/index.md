# Borsuk documentation

Borsuk is a language for services of every size. Coding agents write it. People read it through tools.

## Design

| Document | Content |
|---|---|
| [Language core v0.1](design/language-core-v0.1.html) | The design of the language, version 0.1. Each release builds parts of this design. |
| [Design and roadmap](design/design-and-roadmap.html) | An earlier design page: what Borsuk is for, the five language rules, two syntax candidates, what a check can claim, the booking example, and ten phases in four tracks. The language core design is newer. |
| [Verified FSM language](design/verified-fsm-language.md) | The first design note. It gives the design principles and a review of other work. The language core design is newer. |

## Roadmap

| Document | Content |
|---|---|
| [Milestones](roadmap/milestones.md) | The milestones from v0.0.1 to v0.1.0, the parts that come after v0.1 (many nodes), the implementation stack, and the reasons for the order. |

## Releases

### v0.0.2: canonical bytes and exact numbers

Status: planned.

| Document | Content |
|---|---|
| [Plan](releases/v0.0.2/plan.md) | The contract of v0.0.2: the codec and the Q1 byte-layout experiment, `F64` and `F32` with 18 correctly rounded functions, `(Decimal S)`, the new static rules, the proofs, the corpus and `check.sh`. |

### v0.0.1: core and interpreter

Status: released, tag `v0.0.1`.

| Document | Content |
|---|---|
| [Plan](releases/v0.0.1/plan.md) | The contract of v0.0.1: the core IR grammar, the semantics, the static rules, the proof, the corpus, the layout and `check.sh`. |
| [Goal](releases/v0.0.1/goal.md) | The instructions for the agent that built v0.0.1. |

## Process

| Document | Content |
|---|---|
| [Release goal](process/goal.md) | The standing goal for each release from v0.0.2: the order of authority, the roles, the loop for each phase, the rules, the stop rules and the final report. |
| [Plan review skill](../.claude/skills/plan-review/SKILL.md) | The skill that runs the plan review of the release goal: the author checklist, the reviewer brief, the round protocol and the fix rules. |
| [Commit messages](process/commits.md) | The Conventional Commits rule, the types, the scopes, and the setup of the `cog` tool and its hook. |

## Code

| Path | Content |
|---|---|
| `spec/` | The Lean 4 reference. It builds the executable `brk-ref` and the proof `Borsuk.coverage`. |
| `crates/` | The Rust mirror of the reference. It builds the executable `brk`. |
| `corpus/` | The accepted, rejected and failing programs, with their expected output. |
| `check.sh` | The only gate. Run `./check.sh all` from the repository root. |
