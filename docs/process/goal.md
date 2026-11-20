# Goal: build one Borsuk release

This file is the standing goal for every release from v0.0.2. The owner starts a release with one line:

```
Build Borsuk vV. Obey docs/process/goal.md exactly.
```

In this file, `V` is that version, for example `0.0.2`. The goal is complete when `./check.sh all` passes on `main` and the tag `vV` is on the remote. Then give the final report.

The goal of v0.0.1 is in [`releases/v0.0.1/goal.md`](../releases/v0.0.1/goal.md).

## The language

Each decision serves the goals of the language (design sections 1 and 11):

- Coding agents write Borsuk. People read it through tools.
- Each thing has one canonical form. The set of valid programs for one requirement is very small.
- The rules are strict, so that the compiler can assume much and stay fast.
- Each feature comes with its laws and its evidence. Proofs and checks replace hand-written tests where they can.

## Read first

Read each document completely before any work.

1. `docs/releases/vV/plan.md`, the plan of the release. The plan is the contract.
2. The plans of the earlier releases. Each rule in them stays in force, unless the table of changes in the plan of V changes that rule.
3. The sections of [`language-core-v0.1.html`](../design/language-core-v0.1.html) that the plan names, and design sections 1 and 11.
4. [`milestones.md`](../roadmap/milestones.md).
5. [`commits.md`](commits.md).

## Order of authority

| Rank | Source |
|---|---|
| 1 | The answers of the owner in the current session |
| 2 | This goal. The plan of V can name exceptions to the host rules, to the freeze points and to the mirror rule. |
| 3 | The plan of V |
| 4 | The plans of the earlier releases |
| 5 | The design |
| 6 | The milestones |

A higher rank decides a question that a lower rank does not answer. A disagreement between two sources is a stop (below), also when a higher rank seems to win. A change that the plan of V names in its table of changes to earlier rules, an exception that rank 2 permits, and a place where the plan of V names its difference from the design (a definition, a limit or an owner exception), are not disagreements.

## Plan review

The owner starts a release only after its plan passes the plan review. The skill `plan-review` (`.claude/skills/plan-review/`) runs it:

1. The author applies the author checklist of the skill, verifies each tool fact on the host, and asks the owner about each open choice before the first reviewer.
2. A new Fable reviewer at xhigh effort examines the plan against the design, the milestones, the plans of the earlier releases, this goal and the goals of the language. It reports each finding of the classes below, with the place and a fix.
3. The author applies each finding that the sources support. The owner decides each finding that needs a decision, and each point where two reviewers disagree.
4. At most seven full rounds run, each with a new reviewer. They end early when a full round reports no finding. Then at most three blocking-only rounds run, each with a new reviewer that reports only UNBUILDABLE, CONTRADICTION and NOT-PLANNED findings. The review ends when a blocking-only round reports none. If the third blocking-only round still reports one, the author applies it and asks the owner. More rounds run only when the owner asks.

| Class | Finding |
|---|---|
| NOT-PLANNED | An item, form, keyword, operation, type, module, crate, rule, fault, proof, harness, setting or abstraction that the milestone row, its exit gate, a design sentence or an owner decision does not ask for, and that is not the smallest means to build, test or prove an item that they ask for |
| CONTRADICTION | The plan disagrees with itself, an earlier plan, this goal, the design or the milestones. |
| GAP | A question that changes an output, a byte, a check, a measurement or a decision, and that the plan does not answer |
| WRONG-FACT | A wrong statement about a standard, a tool, a library or mathematics |
| UNBUILDABLE | An item that cannot be built, proved or checked as written |
| WEAK-CHECK | A place that weakens a check or lets an agent skip strictness |
| UNFAIR-EXPERIMENT | A part of a measurement that favors one candidate, or a definition of a measurement that does not match the rule of the design |
| HISTORY | A review round, a date of a decision or a change log in the plan |
| GOAL | A defect of one of these classes in this goal |

The plan states only its latest text: no history, no review rounds and no dates of decisions.

## Roles

| Role | Model | Job | Can edit |
|---|---|---|---|
| Coordinator | this session | Writes the shared files first. Splits each code phase into slices. Integrates the slices. Runs `check.sh` and the gates. Makes the commits and pushes. | Yes |
| Implementer | Opus subagent | One slice: one file of the phase. Gets the plan path, the slice, the Lean module that a Rust file mirrors, the rules sections of each plan in force and the host rules below. | Its slice only |
| Phase reviewer | new Opus subagent | Examines the diff of one phase against the plan. Reports each finding with file and line. | No |
| Gate reviewer | Fable subagent (Agent tool, `model: fable`) | Runs each gate of the plan. | No file in the repository |
| Comment check | `/no-comments` skill | Removes comments and finds workaround code in the phase diff. | Comments only |

- At most three subagents run at the same time. At most two heavy jobs run at the same time, and this count includes the jobs of the coordinator.
- Only the coordinator runs `check.sh` and Kani.
- Two slices that run at the same time never share a file.
- Each subagent gets a narrow brief with file paths. Give each reviewer the files and the plan, not your conclusions.
- A new reviewer examines each phase and each gate. Never reuse a reviewer.

## Start

Before P0, `git status` shows no change, and the plan of V is in a commit on `main`. Else stop and ask.

## Loop for each phase

The plan gives each phase its work, its `check.sh` stage and its gate.

1. Do the work of the phase.
2. Run `./check.sh` with the stage of the phase. Repeat until it passes.
3. If the phase changes code, run `/no-comments` on the phase diff. Apply each accepted finding. Code is each source file in `crates/`, `spec/` and `experiments/`, `check.sh`, and each source file of a tool that the plan names. Measurement data is not code.
4. If the phase changes code, start a new Opus phase reviewer. Give it the plan, the phase name and the diff. Tell it to examine plan conformance, correctness, the mirror rule, each part that the plan does not name, and time, memory and stack use on large and deeply nested inputs.
5. Apply each finding that the plan supports. Write each rejected finding and its reason in the commit body. Then run `./check.sh` with the stage until it passes.
6. Run the gate of the phase, if the phase has one. After a gate finding, correct it and go to step 2.
7. Make one commit on `build/vV`. Add each file by its path. Never use `git add -A` or `git add .`. Push the branch.

The gate classes are "not valid in the grammar", "breaks the plan", "breaks the design", "not in the plan", and each class that the plan adds for a gate. "Not in the plan" is each item, module, function, type, parameter, setting or abstraction that the plan does not name, and that is not the smallest means to build an item that the plan names. A gate passes when the Fable reviewer reports no finding of a gate class.

## Rules

Scope:

- Build each item of the plan and no other item. Do not rename, reorder or skip an item.
- Do not build a part of a later milestone. Do not add a hook, a trait, a parameter or a setting that only a later milestone needs.

Design:

- Think about the whole system before you change a file.
- A local fix that adds a special case, a flag, a wrapper or a second representation is wrong. Find the cause in the shared code. Correct it there.
- Lean is the reference. Rust uses the Lean module names and function names in `snake_case`, and the same rule codes and fault names.

Checks:

- The checks are the corpus, `check.sh`, the Lean proofs and each other check that the plan names. Do not write another test, test helper or mock.
- Do not weaken `check.sh`. Do not skip a step.
- Do not use `sorry`, a new `axiom`, `unsafe`, `@[implemented_by]`, `@[extern]`, `#[allow]`, `#[expect]`, `--no-verify` or a disabled check. Use `partial` only where a plan in force permits it.
- Do not change a lint level, a lint threshold or a tool setting to make a check pass. A setting that the plan names is the only exception.

Frozen files:

- The corpus files and the expected outputs of each release are frozen at the freeze point that the plan names, else after their gate. The plan can freeze more files, for example measurement data.
- A frozen file never changes. This includes the frozen files of earlier releases.
- If a frozen file is wrong, or a change needs a change to a frozen file, stop and ask.

Git:

- Write each commit message in the form of [`commits.md`](commits.md). The `commit-msg` hook runs `cog verify`.
- You can make commits, push `build/vV`, fast-forward `main`, make the tag `vV`, and push `main` and the tag.
- Do not force-push. Do not rewrite pushed history. Do not delete a branch or a tag.

Host:

- Other jobs of the owner share this computer.
- Run each heavy job (fuzz runs, comparisons, proof runs, large builds) under `nice -n 19 ionice -c3`.
- Run at most two heavy processes at the same time. Keep each process below 2 GB. Bound the number of cases.
- Run `check.sh` as `CARGO_BUILD_JOBS=2 LEAN_NUM_THREADS=2 nice -n 19 ionice -c3 ./check.sh STAGE`. `LEAN_NUM_THREADS=2` limits `lake build` to two `lean` processes.
- Run `uptime` before a heavy job. Give each subagent brief these rules.
- A measurement that the plan defines runs as the plan says, on the quiet host that the plan defines.

Documents:

- Write each document and each message to the owner in ASD-STE100 Simplified Technical English.
- A document states only its latest text: no history, no review rounds and no dates of decisions.

Data:

- Never put the project name, the owner's name or a local path in a web search.
- Never send credentials, `.env` files or personal data to a third-party model or a web service.

## Stop and ask the owner

Push the branch first, if the remote accepts it. Then stop. Ask one clear question with the facts when:

- two sources in the order of authority disagree;
- the plan does not answer a question that changes the output of an executable, the bytes of a stored form, the result of a check, a measurement or an experiment decision;
- a gate reviewer finds that the plan is wrong;
- a frozen file of any release is wrong, or a change needs a change to it;
- the plan needs a tool, a library or a data source that it does not name;
- a measurement result is still unclear after the repeat that the plan defines;
- a gate fails three times;
- `./check.sh` fails after five attempts on one cause;
- the install of a tool fails;
- the remote refuses the branch, or `main` cannot fast-forward;
- `./check.sh all` fails on `main` after the merge.

Do not pick an answer. Do not continue.

## Release

The release phase does not use the loop for each phase. It uses these steps:

1. Set the status of V in `docs/index.md` to "released, tag `vV`", in a commit on `build/vV`.
2. Run the release gate of the plan. It examines the full diff of the release, with that commit, against the plan and the design. After a finding, correct it on `build/vV` with steps 2 to 5 and 7 of the loop and the stage `all`. Then run the release gate again with a new reviewer. If the correction needs a change to a frozen file, stop and ask.
3. Merge to `main` with `git merge --ff-only`.
4. Run `./check.sh all` on `main`. If it fails, stop and ask. Do not make the tag.
5. Make the tag `vV`. Push `main` and the tag.

## Final report

Give the owner these items in ASD-STE100 Simplified Technical English:

1. The last `./check.sh all` output.
2. The axiom line of each theorem that `check.sh` examines.
3. The commits on `main` since the start.
4. Each rejected review finding and its reason.
5. Each item of the plan that is not done.
6. Each measurement result and the decision that it gave.
7. Each question that the next release must answer.
