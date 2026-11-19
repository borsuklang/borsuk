# Borsuk milestones: v0.0.1 to v0.1.0

Status: working plan. The design is in `Borsuk-Language-Core-v0.1.html`.

## What the milestones are

- A 0.0.x version is an internal step in the build. It makes no public promise.
- v0.1.0 is the first release. It contains every part of the design, in one release.
- Q1 to Q8 are the eight measurement questions in section 14 of the design.

## Implementation stack

| Tool | Job | First milestone |
|---|---|---|
| Lean 4 | Language semantics, executable reference interpreter, effect soundness proof, mode function M, codec spec | 0.0.1 |
| Rust | Compiler, runtime, tools | 0.0.1 |
| Differential tests | The Lean interpreter against the compiled Rust steps, on generated programs. This is the compiler oracle of the design. | 0.0.3 |
| Kani | Bounded proofs on the real Rust code: no panic or overflow on the hot path, safe `unsafe` code in the arena and the byte layout, codec round trip, small-scope checks of the decision table and the gate. A harness can also run as a fuzz test. | 0.0.2 |
| Verus | Proofs with no bound for a few core runtime algorithms: the decision table, writer epochs and fencing, the output gate, log store invariants | 0.0.7 |
| Aeneas | In reserve. It translates safe Rust into Lean, so it can connect the Rust code to the Lean proofs. It supports only a subset of Rust. | — |

Kani does not check concurrency, async code or FFI. The scheduler and the network stay with simulation and the layer 3 tests.

Until 0.0.4 decides the surface syntax, tests and examples use the core IR as S-expressions. This form is internal and never public. Both candidate syntaxes compile to it.

## Milestones

| Version | Theme | Main contents | Exit gate | Closes |
|---|---|---|---|---|
| **0.0.1** | Core and interpreter | Core IR; pure `fn`, and `fn` with `ConsoleOut`; machines with the full cell table, groups and `impossible`; the envelope; output effects `ConsoleOut` and `Timer`; `by` admission; examples; reference interpreter; in-memory runtime on the `cli` platform; the Rust mirror; proof of cell coverage | Hello world and the Slot machine run in Lean and in Rust with equal traces. The static rules reject every missing cell, and a Lean proof shows it. | — |
| **0.0.2** | Canonical bytes | Codec from types; append-stable layout; format version fields; the three layout variants of the experiment; strict IEEE 754 floats (binary64 and binary32) with correctly rounded math functions; `Decimal` | The layout rule decides the form. A proof shows that encode and decode are inverse. | Q1 byte layout |
| **0.0.3** | Memory and native code | Owned values, update in place, arena, `take` and `copy`; native lowering of steps; mode function M; user generics; bounded collections with `max` and `retain`; `for` | The four test cells meet their limits, or fallback steps 2 to 4 run. The count gives one signature per body. | Q2 test-cell part, Q3 one signature |
| **0.0.4** | Text for agents | Two syntaxes for the experiment (Rust-like and keyword-led) over one core; formatter and normal forms; closed world; modules and `use`; nested patterns; text operations, explicit NFC and one pinned Unicode version; typed holes; table and diagram views; cell hashes | The syntax and the hash rule are fixed. The first public example appears. | Q4 syntax, Q5 local names |
| **0.0.5** | Effects | Request effects; the built-in effects `ConsoleIn`, `Send`, `Log`, `Entropy`; start forms; `fn … uses` lowering with deadlines and `all`; parameter forms; deployment bindings; `Foreign`; recursion through a wait; the runtime timer set that delivers `Fired`; many instances in the in-memory runtime | The Lean proof of effect soundness is complete. The HTTP handler example runs. | — |
| **0.0.6** | Specs and checker | Law forms and the five results; tool order (refute, decide, SMT, Lean); certificates; evidence records; law strength report, witnesses, approval views, contract diff; deterministic simulation with the fault list; coverage records; interpreter oracle; interfaces with laws; `decreases` for recursion in pure functions | Every Slot law is proved. Each law and each outcome has a witness. No cell lacks law protection. | — |
| **0.0.7** | Durable single node | Store contract; memory store and local-disk log; durable step and output gate; decision table, command IDs, windows, client numbering; timers and outbox across a crash; index-neutral checkpoints with replay; `durable local`; `final` states and life numbers | The first byte is stored. Crash simulation keeps every runtime law. First speed run against Rust on one node. | Q2 speed part, Q7 index |
| **0.0.8** | Many nodes | Shards per core; key ranges; router; control plane with consensus; writer epochs and fencing; replicated log store and object-storage log store; `quorum`, `zonal`, `regional`; fresh and stale queries; overload rules | Failover works in simulation and on real nodes. Runtime evidence layer 3 starts. | Q6 scheduler |
| **0.0.9** | Several instances | `pending` and `decide`; transactions with the order log; global protocols with role machines and the proof that no party waits forever; library protocols with `via`; escrow | The Transfer and Order examples run. Laws exist for each feature pair so far. | — |
| **0.0.10** | Upgrades | Code store by hash; `migrate` with proof and `drop`; Activate records; rollout phases; process handoff; shadow run; behavior diff | A live upgrade with a migration runs in simulation and on real nodes. | Q8 code swap |
| **0.0.11** | Personal data and compaction | `personal` fields; per-person keys and key store; erasure deadline; audit archive; compaction pacing, time floors, memory budget, `expire idle` | In simulation, an erasure reaches every copy within its deadline. | — |
| **0.0.12** | Production and QA | Law and contract monitors; contract probes; whole-deployment simulation; agent QA tools; runtime evidence layer 3 complete; outside review | All monitors run on the reference deployment. The proof closure rate is measured. | Proof-automation risk |
| **0.1.0** | The language contract | Everything above; all feature-pair laws; documentation | The speed targets are met. Every v0.1 gate passes. | — |

## Reasons for the order

- The five questions that fix program text or stored bytes close in the order that section 14 requires: 0.0.2, then 0.0.3, then 0.0.4.
- No milestone stores a byte before 0.0.7. By then, every question that fixes bytes or hashes is closed.
- The effect proof comes at 0.0.5, not at the end. A late change to the effect rules would change program text.
- The first speed run comes at 0.0.7, as soon as a durable path exists. This starts the memory fallback steps early, if they are necessary.

## Rules for every milestone

- Rules R1 to R5 from section 16 apply from 0.0.1. Examples: the runtime core is a library that a host calls, and the IR is target-neutral.
- Each feature comes with its laws and its evidence in the same milestone.
- A law for a feature pair comes with the second feature of that pair.
