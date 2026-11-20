# Borsuk · An FSM-first language for distributed systems

Design principles and state-of-the-art review · 18 November 2026

Borsuk is the working name, honoring Polish mathematician Karol Borsuk and his work in topology. [MacTutor biography](https://mathshistory.st-andrews.ac.uk/Biographies/Borsuk/)

## 1. What we want to build

A language for high-throughput, stateful software that many agents can change concurrently. An agent working on one module should be able to read its contract, change its implementation, and discover exactly which behavioral, ownership, compatibility, or resource guarantee it broke. The primary workload is an end-to-end state change: a caller issues a command, the system durably decides it, and the caller can recover a lost reply within the command’s advertised lookup window.

The three original commitments are **strong types across boundaries**, **explicit state machines with functional transitions**, and **strict modularity by default**. Actor-style ownership, efficient mutation and named behavioral specs give the core its semantics. Formal verification belongs to the toolchain. The proposed production architecture uses Rust for the compiler and runtime, a Borsuk-owned intermediate representation, and LLVM for ahead-of-time native code generation. **Surface syntax remains open.** Section 5 uses a worked example to distinguish semantic decisions from notation.

The adoption target is a language that coding agents can learn and use from a short task prompt in an existing project. Rust and Ruby are reference points for how widely the language could be used. The core workload remains verified distributed mutations.

## 2. Language rules and companion tools

A language rule determines whether a program is well formed, what it can do, or what a caller may rely on. Tooling helps people and agents write, check, understand, or ship that program. The standard library and runtime sit at their interface: the language expresses a guarantee, a library selects it for an operation, and the runtime must implement it.

### Five core language rules

| Rule | Obligation |
|---|---|
| **L1. Public boundaries are typed protocols.** | Distinct domain identities, payloads, replies, and legal continuations have types. A single-use handle changes what its holder may do next. A foreign input becomes a typed value only after validation. The exact wire format and SDK are replaceable. |
| **L2. Domain state evolves through explicit, functional transitions.** | Each independently evolving state owner defines its finite control states, associated data, initial state, and permitted edges. A turn consumes state and a typed input and computes a successor and effect descriptions. External results arrive as inputs. Local variables, pure helpers, and scratch data need no actor or mailbox. |
| **L3. Modules are private by default and compose through declared interfaces.** | Each module owns its representation. Dependencies and observable effects cross an explicit signature. A module can use another module's exported guarantees without inspecting its implementation. Composition must discharge environmental assumptions or surface them at the outer boundary. |
| **L4. Ownership and visibility govern mutation.** | A transition may update unique storage in place if this preserves every promised observation, including failure behavior and declared cost bounds. Borrows cannot escape their lifetimes. A successful local ownership handoff publishes prior writes to the receiver. A rejected handoff leaves ownership with the sender. |
| **L5. Named behavioral specs have a conformance meaning.** | A spec can state safety laws, conditional progress, and scoped resource bounds. An implementation must admit the contracted inputs and its observable behavior must refine the spec under its declared assumptions. A caller may rely on a law as proved only with discharged obligations for that scope. Trusted external contracts stay visible as assumptions. An unresolved obligation can remain in a working draft. |

L3 makes the module the boundary of change. L5 defines behavioral substitution across that boundary. Compile-time evidence can be erased when execution does not depend on it. An explicit FSM can still have infinitely many possible configurations through its data.

### What ships with the language

| Component | What it owns |
|---|---|
| **Checker and proof tools** | Type and effect checking, proof obligations, solver or proof-assistant integrations, bounded model checking, counterexamples, simulation, replay and evidence caching. Conformance means the same thing across checker implementations. Evidence reports distinguish proofs, bounded checks, samples, refutations and unknowns. |
| **Compiler and interop tools** | Native code generation, inlining across safe module boundaries, storage reuse, specialized codecs and SDKs. The optimizer must preserve any exported resource bounds and observations. |
| **Agent tools** | Search by intent, version-matched documentation and examples, friendly prompts, typed MCP tools, CLI equivalents and structured diagnostics. Every result identifies the source and spec revision. |
| **Compatibility and delivery tools** | Public-contract diffs, dependency impact analysis, migration checks, CI release policy, and comparison across supported deployment versions. The semantic compatibility relation comes from L5. |
| **Evaluation tools** | Same-guarantee performance benchmarks, fault injection and agent adoption trials. Each measures a property of an implementation or workflow. |

**Runtime and standard-library contracts.** A bounded queue specifies capacity, admission, ownership on every result, and memory visibility. A durable command specifies when its decision takes effect, retry identity, atomicity scope, lookup window and crash assumptions. Those are normative parts of the respective APIs. A pure parser needs neither queue capacity nor a retention policy. A deployment selects the implementations and checks that their guarantees compose.

### How the previous ten items map

| Earlier item | Language | Runtime or tooling |
|---|---|---|
| 1 · End-to-end types | L1 sets the protocol and trust boundary. | Codecs, validators and SDK generation implement it. |
| 2 · Explicit FSMs | L2 defines legal transitions and effect semantics. | Graph rendering and trace views expose them. |
| 3 · Modularity | L3 defines privacy and composition. | Dependency navigation and incremental checking support it. |
| 4 · In-place mutation | L4 defines lawful aliasing and ownership transfer. | The allocator, optimizer and queue realize the chosen representation. |
| 5 · Overload and costs | L4–L5 define ownership outcomes and the meaning of a declared bound. | Queues specify capacity. Static analysis establishes bounds, and profilers measure actual costs. |
| 6 · Durable writes | L2 and L5 can express protocols and failure laws. | The durable-command API and storage adapter choose and honor their commit, recovery and retry contracts. |
| 7 · Formal verification | L5 defines properties, assumptions and refinement. | Verifiers, simulators and replay engines produce different kinds of evidence. |
| 8 · Evolution | L3 and L5 define when a provider can replace another. | Diffing, mixed-version checks and release policy enforce the deployment workflow. |
| 9 · First-class specs | L5 makes specs importable, nameable interfaces. | Proof reports and editors expose them. |
| 10 · Agent adoption | A product goal for the full distribution. | MCP, prompts, documentation, onboarding, benchmarks and adoption metrics. |

## 3. Research behind the ten original design topics

### 1 · Public protocols and end-to-end types

**Ur/Web** demonstrates one type discipline spanning client code, server code, and database access. **Rumpsteak** shows how multiparty session types can check communication order and permit safe asynchronous reorderings under its protocol assumptions. Together they suggest exposing both the *shape of a message* and the *continuation available after it*. A typed hold token tells a client it may attempt confirmation; expiry, duplication over the wire, and concurrent revocation remain authority-side decisions. [Ur/Web, POPL](https://adam.chlipala.net/papers/UrWebPOPL15/UrWebPOPL15.pdf) · [Rumpsteak](https://mrg.cs.ox.ac.uk/publications/deadlock-free-asynchronous-message-reordering-in-rust/main.pdf)

### 2 · Executable, FSM-first semantics

**P** starts from communicating state machines. **PGo** takes a Modular PlusCal description and produces a verification target and executable Go. They are closer precedents for this project than an ordinary typed actor library. Our choice would be to make one typed transition representation authoritative for the interpreter, verifier, trace format, and optimizer. The production claim still depends on correct translation and runtime behavior. [P language and semantics](https://p-org.github.io/P/advanced/psemantics/) · [PGo](https://distcompiler.github.io/)

### 3 · Compositional verification

**P’s module system** composes groups of state machines. **Grove** applies concurrent separation logic to implementation-level reasoning about distributed Go components, including replication and crash recovery. The practical design lesson is to let modules hide their state representations and proof lemmas. A caller gets observable guarantees. At composition time every relied-on assumption needs a provider or an explicit environment assumption; two modules promising progress only if the other moves first need an independent progress argument. [P module system](https://p-org.github.io/P/manual/modulesystem/) · [Grove, SOSP](https://iris-project.org/pdfs/2023-sosp-grove.pdf)

### 4 · Ownership and functional in-place updates

**Rust** sets the data-race-freedom baseline. **Pony** demonstrates transfer of isolated mutable objects and sharing of deeply immutable ones. **Perceus** implements storage reuse for functional programs. **FP²** goes further: its restricted fully in-place calculus guarantees execution without allocation or deallocation and with constant stack space for admitted functions. This is the most direct precedent for the mutation requirement. Offer ordinary pure transitions plus a checked in-place subset for hot paths. Define a local transfer independently from the encoding and copying costs of a cross-process send. [Safe Rust](https://doc.rust-lang.org/nomicon/races.html) · [Pony reference capabilities](https://tutorial.ponylang.io/reference-capabilities/passing-and-sharing.html) · [Perceus, PLDI](https://www.microsoft.com/en-us/research/publication/perceus-garbage-free-reference-counting-with-reuse-2/) · [FP², ICFP](https://www.microsoft.com/en-us/research/wp-content/uploads/2023/05/fbip.pdf)

### 5 · Predictable resource consumption

**Jane Street’s OxCaml** checks allocation across callees and offers a strict mode covering exceptional paths. Its locality and uniqueness modes distinguish values that can escape or be aliased. **Rast** makes resource bounds part of session types under an explicit cost model. A useful first contract is “this local handoff allocates zero heap bytes, including when the queue is full.” Define whether accounting includes payload, queue node, logging, and cleanup. Bounding live memory also requires bounds on retained payload size, outstanding messages, and the number of owners. Wall-clock tail latency needs measurement on target hardware. [OxCaml allocation checker](https://oxcaml.org/documentation/miscellaneous-extensions/zero_alloc_check/) · [OxCaml modes](https://oxcaml.org/documentation/modes/intro/) · [Rast](https://www.cs.cmu.edu/~fp/papers/rast20.pdf)

### 6 · Fast, crash-safe distributed mutations

**RIFL** ties retry identity and durable completion records to the underlying mutation so a retry can recover an already committed result. **Invariant confluence** characterizes when independent updates can merge safely for stated invariants and operations. **vMVCC** demonstrates the proof/performance trade-off in real code: its verified in-memory transaction library achieved 25–96% of Silo’s throughput across the reported workloads. For our design, serialize conflicting claims on the same scarce resource, or partition rights with a proof. Keep independent keys concurrent. External side effects need their own idempotency or reconciliation contract. [RIFL, SOSP](https://web.stanford.edu/~ouster/cgi-bin/papers/rifl.pdf) · [Coordination avoidance, VLDB](https://www.vldb.org/pvldb/vol8/p185-bailis.pdf) · [vMVCC, OSDI](https://www.usenix.org/conference/osdi23/presentation/chang)

### 7 · Formal verification of distributed execution

**PVerifier** proves inductive safety invariants for a model under stated assumptions. **Anvil** verifies a liveness property of executable Kubernetes controllers. **FoundationDB** runs production logic under a deterministic simulator for repeatable failure testing. These support different claims. Expose five possible results: *proved under assumptions*, *exhaustively checked within bounds*, *sampled schedules passed*, *counterexample*, and *unknown*. A simulator failure should replay. An inconclusive proof should expose the unresolved obligation. A passing production trace establishes evidence about that execution. [PVerifier](https://p-org.github.io/P/advanced/PVerifierLanguageExtensions/announcement/) · [Anvil, OSDI](https://www.usenix.org/conference/osdi24/presentation/sun-xudong) · [FoundationDB simulation and testing](https://apple.github.io/foundationdb/testing.html)

### 8 · Agent changes, specification quality, and upgrades

A green proof can survive the removal of its most valuable promise. **MutDafny** checks for weak specifications by introducing faulty implementations and observing which still verify. **DSpec2Test** derives black-box tests from specifications. **TraceLinking** compares implementation traces with formal designs. Amazon’s rollback guidance documents the separate problem of readers, writers, and persisted state coexisting during a rollout. Give agents a semantic contract diff, independently maintained examples and forbidden histories, and an old/new compatibility matrix. A change from “reply after durable commit” to “reply after enqueue” must be visible even when every message has identical bytes. [MutDafny](https://arxiv.org/abs/2511.15403) · [DSpec2Test](https://sr-lab.github.io/publication/2026/ASE2/) · [TraceLinking, OOPSLA](https://www.cs.ubc.ca/~bestchai/papers/oopsla25-trace-link.pdf) · [Rollback safety](https://d1.awsstatic.com/builderslibrary/pdfs/ensuring-rollback-safety-during-deployments.pdf)

### 9 · Native behavioral specifications

A module may export a named `spec`. It defines the public observations, the assumptions on the environment, and the laws over permitted histories. Consumers can import it or take it as a module parameter. A machine declaring `implements` must satisfy the protocol types and show that its observable behavior refines the spec, including any promised progress under the stated assumptions. Several machines can implement the same spec with different private states, algorithms, and storage layouts. A non-executable temporal law is a valid part of a spec.

For example, two laws in a proposed `DurableReschedule` spec could read as follows. Both refer to the decision for a command ID and payload. A subsequent reschedule with a new ID may legitimately move the appointment again.

| Public law | Obligation for each implementation |
|---|---|
| **Acknowledged decisions survive recovery.** | Once a caller receives a committed result, recovery must preserve that decision for its published retention window. A crash between an early acknowledgment and durable commit violates this law. |
| **Retries agree.** | Within that window, every definitive reply to a retry with the same ID and payload must report the original decision. A lost reply leaves the caller free to retry. |

These are safety properties. An implementation that never replies could satisfy both. Give the spec a separate progress clause if accepted commands must eventually receive a recoverable decision, and state the delivery, scheduling, and recovery assumptions needed to establish it.

For an upgrade, check the direction explicitly. A replacement may accept a broader environment and offer stronger guarantees. Requiring more from existing callers or promising them less is a contract change. Keep the public laws stable while the implementer changes private proof lemmas. Prior art includes TLA+ refinement mappings for relating behaviors across abstraction levels and Lean’s `LawfulMonad` for packaging laws about an interface. [TLA+ refinement mappings](https://lamport.azurewebsites.net/tla/proving-safety.pdf) · [Lean interface laws](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/)

### 10 · Agent-first adoption

Rust and Ruby are benchmarks for adoption. The language should earn a place in an existing Rust, Ruby, or other application one workflow at a time. The human describes the outcome. A coding agent can start without knowing a language keyword or a module name.

Ship a discoverable prompt such as **“Make rescheduling safe to retry after a lost reply. Preserve its public contract and show me how you checked it.”** A fresh agent should be able to find the owning module by intent, read the project's pinned contract and one tested example, change the implementation, and replay a failing schedule. The prompt is reusable guidance. The public spec supplies authority over behavior.

| Agent need | Proposed interface |
|---|---|
| Find the owner and learn the idiom | A search tool accepts intent or an exact symbol. It returns the owning module, stable spec and law IDs, the package version, and links to compact docs and examples checked against that version. |
| Check a change | A verification tool invokes the same checker as CI. Its structured result identifies the input revision, dependency and toolchain identity, affected laws, assumptions, proof status and bounds. Diagnostics carry source spans, the observed violation, and candidate repairs when available. |
| Understand a failure | A replay tool runs the counterexample using its recorded inputs, versions, and schedule. Prompts such as “explain this failure” can guide the agent to that tool. The CLI exposes the same operation for clients with incomplete MCP support. |

MCP already distinguishes prompts, resources, and callable tools. Host support and context selection vary, so the search tool should work even when a host does not proactively attach documentation resources or prompt templates. Rust's machine-readable diagnostics are a precedent for structured spans and suggestions. Anthropic's tool-design work recommends measuring tools on realistic agent tasks. [MCP server primitives](https://modelcontextprotocol.io/docs/learn/server-concepts) · [MCP resources](https://modelcontextprotocol.io/specification/2026-07-28/server/resources) · [rustc JSON diagnostics](https://doc.rust-lang.org/rustc/json.html) · [Evaluating tools for agents](https://www.anthropic.com/engineering/writing-tools-for-agents)

## 4. An end-to-end acceptance case

**Reschedule one appointment under contention.** This exercises the two meanings of mutation in one workflow. Two clients compete for a destination slot. A stale timer from an earlier hold arrives. The winner’s commit reaches durable storage, its reply is lost, and the owner restarts during a rolling upgrade. The ingress queue fills while the client retries.

| Check | Required outcome |
|---|---|
| Client and protocol | The client keeps the same command ID across retries. A timeout leaves the result unknown. After a decision the service retains it for the specified lookup window. A definite rejection preserves the original appointment. Foreign clients go through the same wire validation and replay checks. |
| Atomic, externally visible mutation | At most one booking owns the destination. A successful move releases the old slot and claims the new one as one logical operation. Define whether the deployment uses a common transaction boundary or a cross-shard protocol, and verify that implementation against the same public history. |
| Failures and recovery | A delayed timeout for hold A cannot release hold B. After commit and crash, retry returns the original durable decision within the advertised recovery window. For a recognizably expired request ID, return `OutcomeExpired` and prevent reexecution. Notifications may be redelivered; their external guarantee states what the downstream service supports. |
| Efficient local mutation | Decode into a preallocated packet. Queue admission transfers ownership on success and returns ownership on rejection. Check conservation of all pool buffers, including queued and in-flight packets. Verify the declared local allocation bound on both branches. |
| Progress and overload | When its recovery, delivery and scheduling assumptions hold, every durably admitted command eventually reaches a durable decision. Declare when an eligible request must be admitted and when overload permits rejection. Retries reaching the service during the lookup window can retrieve a decided result. Keep acceptance, completion and receipt distinct. |
| Real deployment and change | Exercise real codecs, storage adapters, rolling versions, and the client retry path. Replay a simulator counterexample against the smallest reproducible configuration. Compare client-observed histories with the protocol. |

Benchmark against a hand-written Rust implementation with the **same durability, batching, overload policy, hardware, and failure workload**. Report offered and completed throughput, p50/p99/p99.9 end-to-end latency, rejection rate, bytes allocated or copied, and recovery time. Include hot-key skew and saturating offered load. Measure agent usability separately: give an agent only the relevant public signatures and a change request, then see whether it can make the change without weakening guarantees or opening unrelated modules. Do not claim lower latency or better agent productivity before measuring either.

## 5. Production architecture, syntax exploration, and performance targets

### Production compilation and execution

The intended product is a native language for distributed mutations, embeddable one module at a time. Borsuk owns the semantics from source through optimization. Rust is the proposed implementation language for the compiler, runtime and shared tooling. The production backend lowers Borsuk directly to LLVM IR and emits native code ahead of time.

| Component | Responsibility |
|---|---|
| **Borsuk frontend and typed IR** | Resolve types, state variants, input policies, ownership, effects and resource obligations. Keep those facts available while choosing layouts, specializing calls, reusing storage, and fusing compatible transitions. The public protocol and its laws are independent of the machine's private representation. |
| **Reference interpreter and verifier** | The interpreter supplies a simple execution of the typed IR for differential tests and trace replay. Give the verifier a precise interpretation of the same operations. Use Lean 4 selectively for core metatheory, such as preservation of ownership across a well-typed step. Verus is a candidate for selected Rust runtime components. Comparing interpreter and compiled traces gives empirical evidence; claims of compiler correctness need their own refinement argument. |
| **Native backend** | Choose compact representations and lower calls and transitions directly to LLVM. Use cross-module and profile-guided optimization where measured workloads benefit. Check target-dependent resource contracts against lowered code, covered callees and runtime entry points. Report assumptions introduced by foreign code. [LLVM IR](https://llvm.org/docs/LangRef.html) · [ThinLTO](https://clang.llvm.org/docs/ThinLTO.html) |
| **Rust runtime** | An embedded synchronous machine can run on its caller's thread using caller-provided memory. Independent scheduling uses an explicit bounded mailbox. An in-process transfer can move an owned buffer. A process boundary introduces encoding and transport costs. Sharding, batching and group commit remain subject to the protocol's visibility and durability guarantees. |
| **Agent-facing toolchain** | The CLI, MCP interface and CI call the same Rust library for semantic queries, verification and replay. A result has the same law ID, assumptions, evidence status and scope at each entry point. |

For example, an embedded transition from `Held` to a same-size successor on uniquely owned storage should compile down to a tag check, a guard and the required stores. For that scoped path, target zero heap allocations, zero payload copies and zero scheduler hops. A proof erased at build time adds no runtime instructions. A durable reply still incurs whichever storage or quorum costs its contract requires. An allocating diagnostic on a queue-full branch must invalidate an all-path zero-heap-allocation promise. [Verus project and scope](https://github.com/verus-lang/verus) · [FP² and fully in-place execution](https://www.microsoft.com/en-us/research/wp-content/uploads/2023/05/fbip.pdf)

### Surface syntax is an open design question

The semantic requirement is that a reader or agent can see the source state, triggering input, successor, reply and requested effects. Ordinary functions and data manipulation should stay lightweight. Keywords, punctuation, grouping and alignment are all provisional. Once a syntax is chosen, give it a canonical transition form and a formatter so equivalent edits produce predictable diffs.

**Candidate A · one edge per declaration.** This is a notation specimen. The worked example defines a nominal reading type, a public history law, and a private two-state implementation.

```borsuk
module telemetry.peak

pub type Reading = distinct i64 derives Ord

pub spec Peak {
    event Sample(Reading)
    query Read() -> Option<Reading>

    law read_peak {
        Read() returns history.values(Sample).max()
    }
}

machine PeakTracker implements Peak {
    state Empty | Seen(Reading)
    init Empty

    on Empty    + Sample(x) -> Seen(x)
    on Seen(hi) + Sample(x) -> Seen(max(hi, x))

    on Empty    + Read() -> stay, reply None
    on Seen(hi) + Read() -> stay, reply Some(hi)
}
```

The law ranges over the samples processed by this machine before each read in its observable history. The maximum of an empty history is `None`. Histories exist for specification and proof; the machine holds only its current maximum. A new input such as `Reset` should produce diagnostics for each state still missing an input policy.

**Candidate B · group reactions by source state.** The fragment below expresses the same two `Seen` edges. Grouping makes a state's available actions easier to inspect; the one-edge form above makes a transition portable as a self-contained line in a review.

```borsuk
state Seen(hi) {
    on Sample(x) -> Seen(max(hi, x))
    on Read()    -> stay, reply Some(hi)
}
```

Either notation needs to make the ordering of effects readable. In the booking example, `Held(id) + Confirm` enters `Committing(id)` and requests `Persist(id)`. A matching later `Persisted(id)` input permits the success reply. Put that workflow and its failure branches through the same syntax comparison before adopting either form.

### Optimization permitted by the protocol

For the input sequence `Sample(70), Sample(90), Sample(80), Read(), Sample(120), Read()`, the replies must be `Some(90)` and `Some(120)`. Within a contiguous run of samples, repeated applications of `max` can be combined. The reduction starts from the prior maximum, handles the empty state, consumes every incoming reading, and updates the stored result once per run. This can eliminate per-event dispatch and intermediate stores. A contiguous numeric batch may also admit SIMD. Rust and Borsuk can both benefit from LLVM's vectorizer. Borsuk's proposed advantage is exposing the legality of the reduction before machine-code generation. [LLVM vectorizers](https://llvm.org/docs/Vectorizers.html) · [rustc code generation](https://rustc-dev-guide.rust-lang.org/backend/codegen.html)

A read splits the run. So does any applicable guarantee that exposes an intermediate result, such as an individual acknowledgment, a durable log record, an externally visible effect or an ordering obligation to another participant. The optimizer must establish observational equivalence against the defined source semantics, including failures and resource bounds. A public law that omits an observable effect cannot by itself authorize erasing it. Enabling fusion must also respect the same batching and latency budget as the baseline.

### What would justify a performance claim

**Proposed release targets, currently unmeasured:** at least 95% of expert hand-written Rust's completed throughput and at most 110% of its p99.9 latency on a declared representative workload suite. Compare latency at the same offered load and rejection policy. Compare sustainable throughput at the same latency and rejection limits. Report each workload separately so an average cannot hide a slow hot path.

| Implementation of the peak workload | What the result would establish |
|---|---|
| Idiomatic Rust processing one event at a time | Baseline cost of straightforward event-by-event code. |
| Expert Rust with an explicitly fused maximum reduction | Baseline for a developer who has already exploited the same protocol law and batching opportunity. |
| Borsuk compiled from the explicit FSM | Matching the hand-fused version while improving on event-by-event Rust demonstrates automation of the optimization. Reliably beating the hand-fused version supports a faster-than-Rust claim for this workload and configuration. |

Publish hardware, compiler versions and settings, workload distributions, batch limits, failure schedules, semantic checks, and variation across repeated runs. Measure the embedded transition separately from the durable rescheduling workload in section 4. For that second workload, match durability, group commit, skew, overload and recovery behavior across implementations. Neither target attainment nor a speed advantage over Rust has been demonstrated.

The durable acceptance case retains a simple regression test. Move the success reply from after commit to immediately after enqueue. Local message types and the happy path can still be correct. A crash between reply and commit violates the public guarantee, and the agent should receive the corresponding trace.

## 6. Adversarial review

**Verdict.** The architecture appears compatible with the clarified adoption goal. The previous wording allowed conflicting interpretations of recovery and progress. The current wording below gives those promises distinct scopes. Three finite models expose what can go wrong. They model candidate interpretations and a proposed MCP integration. The language has no complete formal semantics, and this review establishes no language-wide consistency proof.

### Counterexamples actually run

Each row reports breadth-first enumeration of all reachable states in both finite variants, with each distinct state counted once. The third model tests the proposed evidence workflow. Its edited revision is stipulated to violate the law, so it tests evidence acceptance independently of solver performance.

| Model and bounds | Shortest failure in the permissive variant | Result with the proposed correction |
|---|---|---|
| One command ID, one credit per command, two deliveries, durable balance and result record, optional crash after an unrecorded effect | Apply credit → crash and restart → retry applies credit again. Identical definitive replies alone do not establish a single application of the mutation. 8 reachable states. | Make the mutation and completion record one recoverable commit. No duplicate application in 3 reachable states. The commit is an abstract primitive in this test. Its storage implementation needs separate evidence. |
| Two peers, two sends each before either peer may receive, one FIFO per direction | A sends once → B sends once. Both queues are full. Neither peer can send its second item or take its first receive. Fair scheduling cannot enable a disabled transition. 4 reachable states at capacity 1. | At capacity 2 all 19 reachable states were explored with no unfinished deadlock. This establishes the capacity threshold only for this protocol. Check the deployed capacities or permit receives while the sender waits. |
| One public law, implementation revisions A and B, one cached proof, one release decision | Prove A → edit to B → accept A's proof for B by law name. 7 reachable states. A stable name helps discovery but cannot identify proof evidence. | Requiring an exact revision match prevents acceptance for B in all 6 reachable states. A production evidence key must also bind semantics-affecting dependencies, assumptions, target, toolchain, and verification settings, or justify reuse by a checked equivalence. |

The write model caps attempts at two and the effects at one credit per execution. Only the split variant has pending work that can be lost at the modeled crash. The queue model tracks each peer’s sends and receives between zero and two. A stuck full send models a protocol which must retry before receiving. The proof model allows a single edit and caches evidence only for revision A. For each comparison the property is deliberately narrow. These experiments exercise no real persistence adapter, MCP client, language implementation, or hardware. Further reading includes [RIFL on recoverable RPC completion](https://web.stanford.edu/~ouster/cgi-bin/papers/rifl.pdf) and [bounded communicating session automata](https://spiral.imperial.ac.uk/entities/publication/98f48268-81c8-4ad2-bea3-0e8abb3cc6dd).

### Consistency decisions and limits

- **Decision, retrieval, and receipt are distinct.** In the reschedule example, durable admission carries an eventual-decision obligation under explicit assumptions. The lookup window starts at the decision. Unbounded network delay can carry a client's retry past that window. Recognizably expired IDs return `OutcomeExpired` and cannot reexecute the command. The runtime must retain sufficient evidence or use an enforceable expiry scheme. An expired lookup does not undo a committed business effect.
- **A bounded queue can reject new work.** Specify the conditions requiring admission as well as progress after admission. Fair scheduling cannot unblock a protocol with no enabled action. Each configured queue capacity participates in the progress argument.
- **Conformance and evidence have different jobs.** A property has a meaning even when a verifier returns unknown. Callers can rely on proved guarantees within their assumptions. Scoped finite evidence cannot discharge an unbounded guarantee. A release policy decides whether a module with unresolved obligations can ship and how to label it.
- **Ownership permits destructive reuse; persistence adds obligations.** If a physical update may survive a crash or become visible through another observer, prove that the adapter preserves the abstract commit semantics. Logging or copy-on-write may be necessary. The runtime's memory ordering and foreign interfaces are part of the trusted boundary unless separately verified.

### A finite witness for compatibility

A separate breadth-first check explored a nontrivial instance of the combined rules. Two distinct request IDs compete once for one slot. A one-entry durable inbox admits either request when free. The owner can crash and restart, commit a pending request atomically, lose a reply, serve a retry, and expire a decided ID. The business owner and per-ID statuses survive restart. IDs are fixed and recognizable after expiry; this example uses finite tombstones.

The model reached **38 states and 106 labeled transitions**, including successful wins by either caller on different schedules, overload, rejected claims, retries and expiry. It found no violation of single ownership, inbox capacity, consistency of definitive replies with the owner, crash preservation, or terminal expiry. Every up state with a pending request enabled its decision. With eventual continuous uptime and weak fairness for that continuously enabled action, a pending request eventually decides. This reasoning assumes an atomic durable commit. The run demonstrates compatibility for this abstract service. A full language still needs formal typing and evaluation rules, soundness results, and a refinement argument for its runtime.

### Performance feasibility

The rules permit efficient native code. A concrete transition on an unaliased fixed-size record can compile to tag inspection and a few stores. A module call can inline. A proof checked ahead of time can add zero runtime instructions. Resource annotations need a defined cost model, including the target and covered callees. Supporting a general allocating function is compatible with requiring zero heap allocations for a particular transition.

Precedents establish individual ingredients. FP² proves fully in-place execution for an admitted functional calculus. OxCaml checks zero OCaml-heap allocation across calls. The verified in-memory vMVCC implementation reports 25–96% of Silo’s throughput on its published workloads. These results support feasibility and also show how wide the performance range can be. [FP²](https://www.microsoft.com/en-us/research/wp-content/uploads/2023/05/fbip.pdf) · [OxCaml](https://oxcaml.org/documentation/miscellaneous-extensions/zero_alloc_check/) · [vMVCC](https://www.usenix.org/conference/osdi23/presentation/chang)

Durable acknowledgement may require a storage flush or quorum, and crossing a trust boundary requires validation. Contended keys, cache locality, code generation and rollout settings affect measured performance. The language defines which optimizations are legal. The end-to-end benchmark in section 4 determines how close a particular implementation gets to hand-written Rust under equal semantics. There is no implementation benchmark for the proposed language yet.

### Adoption test

Give a fresh agent in an existing service the natural-language retry task above. Run repeated trials with the same model, repository, tools budget, and held-out behavioral checks. Compare (a) existing host-language workflow, (b) the proposed language with local docs and CLI, and (c) the same language and checker with guided prompts and MCP. Include stale docs, full queues, changed revisions, and an available shortcut that weakens the public law. Grade the final change and the accuracy of its verification claims independently of its narrative. Record verified task success, false proof claims, human interventions, elapsed time, and tokens. For actual adoption, observe how many pilot teams choose a second workflow after the first succeeds. These are proposed evaluations. No agent benchmark or adoption trial has been run.
