# Goal: build Borsuk v0.0.1

Build Borsuk v0.0.1 in `/home/navaro/Workplace/borsuk`. Obey [`plan.md`](plan.md). Finish the phases P0 to P4. The goal is complete when `./check.sh all` passes on `main` and the tag `v0.0.1` is on the remote.

## Read first

1. [`plan.md`](plan.md). Read all of it before any work.
2. [`language-core-v0.1.html`](../../design/language-core-v0.1.html), the design.
3. [`milestones.md`](../../roadmap/milestones.md). It lists the parts of later milestones.

## Roles

| Role | Model | Job | Can edit |
|---|---|---|---|
| Coordinator | this session | Writes P0, P1 and P2. Writes `lib.rs` and `ir.rs` before the other P3 slices start. Splits P3 into slices. Integrates the slices, runs the gates, commits and pushes. | Yes |
| Implementer | Opus subagent | One slice: one Rust file. Gets the plan path, the slice, the Lean module of the slice and section 9 of the plan. | Its slice only |
| Phase reviewer | new Opus subagent | Examines the diff of P2 or P3 against the plan. Reports each finding with file and line. | No |
| Gate reviewer | Fable subagent (Agent tool, `model: fable`) | Runs gates G1, G2 and G3. | No |
| Comment check | `/no-comments` skill | Removes comments and finds workaround code in `crates/` and `spec/`, in P2 and P3. | Comments only |

At most three subagents run at the same time. Two slices that run at the same time never share a file. Each subagent gets a narrow brief with file paths. Never put the project name, the owner's name or local paths in a web search.

## Loop for P0 to P3

1. Do the work of the phase.
2. Run `./check.sh` with the stage of the phase. The stage is `setup` for P0 and P1, `lean` for P2, and `all` for P3 and P4. Repeat until it passes.
3. In P2 and P3, run `/no-comments` on the phase diff. Apply each accepted finding.
4. In P2 and P3, start a new Opus phase reviewer. Give it the plan, the phase name and the diff.
5. Apply each finding that the plan supports. Write each rejected finding and its reason in the commit message. Then run `./check.sh` with the stage until it passes.
6. Run the gate of the phase, if the phase has one. After a gate finding, correct it and go to step 2.
7. Make one commit on `build/v0.0.1`. Add each file by its path. Never use `git add -A` or `git add .`. Push the branch.

P4 follows its row in the plan. The corrections from gate G3 go through steps 2 to 7, with steps 3 and 4 as in P3.

The gate classes are "not valid in the IR grammar", "breaks the plan" and "breaks the design". A gate passes when the Fable reviewer reports no finding of a gate class.

## Rules

- Build each item of the plan and no other item. Do not rename, reorder or skip an item.
- Think about the whole system before you change a file. A local fix that adds a special case, a flag, a wrapper or a second representation is wrong. Find the cause in the shared code. Correct it there.
- Do not weaken `check.sh`. Do not skip a step. Do not use `sorry`, `#[allow]`, `--no-verify` or a disabled check.
- Write each commit message in ASD-STE100 Simplified Technical English. Give it an imperative subject of 60 characters or less and a short body. End it with the Co-Authored-By line of the session that commits.
- You can make commits, push `build/v0.0.1`, fast-forward `main`, make the tag `v0.0.1`, and push `main` and the tag. Do not force-push. Do not rewrite pushed history.

## Stop and ask the owner

Push the branch first, if the remote accepts it. Then stop. Ask one clear question with the facts when:

- the plan and the design disagree;
- the plan does not answer a question that changes the output of an executable;
- a gate reviewer finds that the plan is wrong;
- a frozen file is wrong;
- a gate fails three times;
- `./check.sh` fails after five attempts on one cause;
- the install of a tool fails;
- the remote refuses the branch, or `main` cannot fast-forward.

Do not pick an answer. Do not continue.

## Final report

Give the owner these items in ASD-STE100 Simplified Technical English:

1. The last `./check.sh all` output.
2. The axiom output of `Borsuk.coverage`.
3. The commits on `main` since the start.
4. Each rejected review finding and its reason.
5. Each item of the plan that is not done.
