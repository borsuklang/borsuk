---
name: plan-review
description: Review a Borsuk release plan (docs/releases/vV/plan.md) and the release goal before the build starts, with few rounds. Use when the owner asks to review, check, harden or finish a release plan, when a new plan is ready for the plan review of docs/process/goal.md, or before "Build Borsuk vV". It gives the author checklist, the decision pass, the Fable reviewer brief, the round protocol, the fix rules and the stop rule.
---

# Plan review

The plan review of `docs/process/goal.md` must end in few rounds. The v0.0.2 plan needed 20 rounds. Most findings came from three causes:

1. Owner decisions that came up late, one round at a time.
2. Details that the plan did not fix, mostly in the measurement, the corpus generators, the Kani checks and the gates.
3. New text that each fix added, which the next reviewer found new gaps in.

This skill removes these causes before the first reviewer, and it limits the rounds.

## Inputs

- `V`, the release, and its plan `docs/releases/vV/plan.md`.
- `docs/process/goal.md`: the finding classes in "Plan review", the language goals in "The language", the rules.
- The milestone row of V in `docs/roadmap/milestones.md`, its exit gate and the implementation stack.
- The design sections that the plan names, and the plans of the earlier releases.

## Protocol

### Round 0: author pass (no subagent)

1. Apply each item of [author-checklist.md](author-checklist.md) to the plan. Each item comes from a defect that a reviewer found in v0.0.2.
2. Verify each tool fact on this host before the plan states it:
   - a crate version and its features: `curl -s -A generic-client https://crates.io/api/v1/crates/NAME/VERSION`;
   - a tool option: `TOOL --help`;
   - an installed toolchain: `rustup toolchain list`, and the toolchain that the tool needs (for Kani: `~/.kani/kani-*/rust-toolchain-version`);
   - a host command: run it once with a tiny case (for example a memory limit with `systemd-run --user --scope -p MemoryMax=64M`).
3. Find each open choice: a question that changes an output, a byte, a check, a measurement or a decision, and that the milestone row, the design and the earlier owner decisions do not answer. The list in [author-checklist.md](author-checklist.md), "Owner decisions", names the kinds that v0.0.2 met late.
4. Ask the owner about all open choices before round 1. Use AskUserQuestion with at most 4 questions in each call, the recommended option first, and the facts in each question. Write each answer into the plan as a rule, with no date and no "the owner decided".
5. Keep a decision ledger in the scratchpad: one numbered line for each owner decision. The ledger goes into each reviewer brief. It is not in the plan.

### Rounds 1 to 7: full review

For each round, start a new reviewer:

- Agent tool, `subagent_type: general-purpose`, `model: fable`, `effort: xhigh`, `run_in_background: true`.
- Prompt: [reviewer-brief.md](reviewer-brief.md), with each placeholder filled.
- Never reuse a reviewer. Give it the files and the ledger, not your conclusions.

An xhigh round takes about 25 to 40 minutes. Wait for its notification, then triage.

Run at most 7 full rounds. The full rounds end early when a full round reports no finding.

### Triage after each round

1. Verify each fact that the reviewer states about the host or a tool before you act on it.
2. Apply each finding that the sources support. Use the fix rules below.
3. Send to the owner, in one AskUserQuestion batch:
   - each finding that needs an owner choice;
   - each pair of reviewers that give opposite advice on one point (v0.0.2: the integer classes and the kind of mean flipped between rounds).

   Add each answer to the ledger.
4. Reject a finding only with a reason from the sources. Keep the reason in a scratchpad triage log. If the next reviewer would raise it again, put the fact or the decision into the next brief.
5. Close each "unconfirmed" risk of the report that a short host check or a one-sentence rule can close.
6. Report to the owner in ASD-STE100: the count per class, the main changes and the decisions that you need. Do not paste the reviewer report.

### Then at most 3 blocking-only rounds

Use the same brief with the blocking-only part of [reviewer-brief.md](reviewer-brief.md): only UNBUILDABLE, CONTRADICTION and NOT-PLANNED, and the answer "NO BLOCKING FINDINGS" when there is none. Each blocking-only round has a new reviewer.

- Apply each blocking finding, then start the next blocking-only round.
- The review ends when a blocking-only round reports no blocking finding.
- If the third blocking-only round still reports a blocking finding, apply it, then stop and ask the owner how to continue.

### Stop and commit

Ask the owner to approve the commit: a branch, one Conventional Commit (`docs: ...`, see `docs/process/commits.md`), push, fast-forward `main`, push `main`. The goal needs the plan in a commit on `main` before P0.

## Limits

- At most 7 full rounds, then at most 3 blocking-only rounds. More rounds only when the owner asks.
- A Fable usage limit stops a reviewer. Tell the owner the reset time. After the reset, resume the same reviewer with SendMessage. Do not use another model without the consent of the owner.
- A reviewer runs no build, no benchmark and no heavy job. It can read files and run `--help` and other small read-only commands.

## Fix rules

These rules keep each fix from adding new defects.

1. Use the smallest fix: the replacement text of the reviewer, or shorter.
2. Before you add a mechanism (a mode, a check, a file, a form, a theorem), test it as a NOT-PLANNED item. If no milestone text, exit gate, design sentence or owner decision needs it, remove the item that needs it instead.
3. After each fix, search the plan for each other place that names the same thing (`grep -n`), and correct them all in the same edit.
4. Give a number in one place only. If it must occur two times, check that both agree.
5. Keep one canonical form. If two forms do the same job, remove one.
6. Keep the plan free of history: no dates, no review rounds, no "owner decision" labels. A rationale sentence is fine.
7. Write the plan in ASD-STE100, and keep each rule testable by an agent: a command, a count, a byte, a file.
