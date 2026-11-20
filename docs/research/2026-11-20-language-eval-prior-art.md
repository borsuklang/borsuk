# Prior art for a later eval of the new language: tokens and errors against established languages

Date: 2026-11-20. Status: research note. It is not a decision.

Scope: "the new language" is the backend language that coding agents write (typed state machines, pure step functions, durable machines). This note does not name it in a link or a query.

Method: five sweep agents searched by angle: backend tasks, multi-language evals, token metrics, new-language evals, and harnesses with statistics. A verify pass then checked each candidate at its primary source on 2026-11-20. This note keeps only the candidates that the verify pass confirmed or corrected, and it applies each correction. I did not open the URLs again. The last line lists the sweep claims that the verify pass refuted.

Tags: [R] is a research fact, with its link. [A] is my assumption or my proposal. An [A] item is never a requirement.

| Term | Meaning in this note |
|---|---|
| Arm | One language condition of the experiment, for example "the Go arm". |
| Oracle | The check that decides pass or fail: tests, exploits, or a verifier. |
| Language-agnostic oracle | An oracle that reads only external behaviour (HTTP, or stdin and stdout). It works for each language without change. |
| Harness | The runner. It starts a container, runs the agent, runs the oracle, and logs the result. |
| Scaffold | The agent loop around the model, for example mini-swe-agent or Claude Code. |
| Repair round | One checker or test result that goes back to the agent, and the edit after it. |
| Habit error | A construct from another language in a program of the target language, for example an "if" or a "return" in the new language. |
| Tokens per solved task | All tokens of all runs, failed runs included, divided by the number of solved runs. |
| pass@k | The probability that at least one of k runs passes. |
| ICC | Intraclass correlation: the share of the variance that comes from the task. |
| LMM | Linear mixed model: a regression with fixed effects (the language) and random effects (the task). |
| SE, CI | Standard error; confidence interval. |
| Contamination | Task text or solutions in the training data of a model. |

## 1. Question

Which parts of existing evals can we reuse for the later eval of the new language? The parts are task sets, test oracles, harnesses, and statistics. The eval compares the new language with Rust, Go, TypeScript, Python, and Java on backend and service tasks. It must support two claims:

1. Fewer tokens: output tokens and total tokens per solved task, repair rounds included.
2. Fewer errors: compile, type, and check errors, test failures, habit errors, and retries.

The note prefers work from 2025 and 2026. It says when a newer item replaces an older item.

## 2. Short answer

No published eval does the full job. The multi-language backend sets (BaxBench, AutoBaxBench) report no tokens [R](https://github.com/logic-star-ai/baxbench). The newest backend set with token columns (BackendForge) uses Python only [R](https://arxiv.org/abs/2607.11042). StaminaBench has tokens and HTTP tests, but Python is its default language [R](https://github.com/amazon-science/StaminaBench). Thus we must assemble the eval from parts [A]. Reuse these parts, in order of value:

| Rank | Item | Part to reuse | Why |
|---|---|---|---|
| 1 | Harbor | The harness for every arm | Apache-2.0. One task format: a Dockerfile and a test script. It logs input, cache, and output tokens and USD for each trial. A test script can write a multi-dimensional reward.json. It has a flag for attempts (-k) and a regrade command [R](https://github.com/harbor-framework/harbor) [R](https://docs.harborframework.com/tasks/overview.md). |
| 2 | BaxBench and AutoBaxBench (AutoBaxBuilder) | Backend scenarios, the HTTP oracle, and a scenario generator | MIT. The tests and exploits are "agnostic to frameworks and programming languages" [R](https://arxiv.org/abs/2502.11844). A new language is one Env [R](https://github.com/logic-star-ai/baxbench). The generator makes a fresh scenario for about USD 3.9 in about 2 h, so no arm saw it in training [R](https://arxiv.org/abs/2512.21132). |
| 3 | BackendForge | The task format and the newest backend tasks | Apache-2.0, 56 tasks, released. A task is spec.md, openapi.yaml, and hidden HTTP tests at four cumulative oracle levels. It reports Cost/Task and Output Tokens/Task. The Python rule is only in the prompt [R](https://github.com/PKU-ASE-RISE/BackendForge) [R](https://github.com/PKU-ASE-RISE/BackendForge/blob/main/docs/EVALUATION.md). |
| 4 | Tokenmaxxing study (Wu, Anderson, Guha) | The token metric and the statistics protocol | The only controlled study of agent tokens across languages. It uses the same tasks in each arm and one scaffold. It counts tokens per success with failed runs included. It fits an LMM on log tokens with a random intercept for each problem [R](https://arxiv.org/abs/2607.22807). |
| 5 | CangjieBench and the PLC metrics | The habit-error method and the reference-in-context setup | The closest analogue to our setting: a language outside the training data, a 2,146-token reference in the prompt, and a "Syntax (foreign)" failure class. MIT, with a Harbor task suite [R](https://github.com/cjhCoder7/CangjieBench). PLC adds metrics for the language that a drift goes to [R](https://arxiv.org/abs/2503.13620). |
| 6 | StaminaBench | Stateful service change and repair rounds | A generator of fresh REST scenarios with 100 change turns. HTTP tests made without an LLM. Retries with graded feedback. The licence is CC BY-NC 4.0, which is non-commercial [R](https://github.com/amazon-science/StaminaBench). |
| 7 | RealWorld Conduit and Constraint Decay | A portable spec and structural verifiers | The RealWorld OpenAPI spec with Hurl and Bruno suites is MIT [R](https://github.com/realworld-apps/realworld). Constraint Decay shows how to add rule levels and a verifier on the diff [R](https://arxiv.org/abs/2605.06445). |
| 8 | A statistics set | Paired, clustered, multi-arm, and power methods | Miller, Wang, Mandujano Reyes, Kotawala, and Hardy et al. See section 7. |
| 9 | The metaprogramming study and EsoLang-Bench | A threat model and a hidden-test protocol | Strong agents avoid an unfamiliar language: they write a Python generator for the target code. The eval needs a policy for this before the first run [R](https://arxiv.org/abs/2606.10933). |

We must write one task family ourselves: durable machines with logs, timers, retries, and an output gate. The sweep found no benchmark for it [A].

## 3. Verified candidates

"Date" gives the first version and the latest version or release. "Effort" is the effort to add the new language as one more arm.

### 3.1 Backend benchmarks

| Name | Date | What it measures | Languages | Oracle | Token reporting | Effort | Licence | Source |
|---|---|---|---|---|---|---|---|---|
| BackendForge | v1 2026-07-13; Findings of EMNLP 2026; repo push 2026-09-10 | An agent builds a deployable service from spec.md and openapi.yaml. 56 tasks, 2,345 API operations. Final oracle: GPT-5.5 passes 16/56, Claude Opus 4.7 10/56, each other configuration at most 3. | Python, by a rule in the prompt. The prepare and evaluate commands accept the output of any agent. | Hidden black-box HTTP pytest at four cumulative levels (Base, +R1, +R2, Final). The released final oracle has 7,839 tests; the paper says 7,890. Five tasks use mock services. | Cost/Task and Output Tokens/Task (GPT-5.5: USD 3.39, 51.06K; Opus 4.7: USD 5.55, 75.38K). Each run writes trajectory.json and results.json. Default: mini-SWE-agent 2.2.8, 500 model calls. | Low: change the prompt and the Docker image. | Apache-2.0 (repo) | [R](https://arxiv.org/abs/2607.11042) [R](https://aclanthology.org/2026.findings-emnlp.2236/) [R](https://github.com/PKU-ASE-RISE/BackendForge) |
| StaminaBench | v1 2026-06-17; repo push 2026-08-05 | How many schema-change turns an agent survives on a REST server. 20 seeded scenarios with 100 turns each; the code grows to about 6,000 lines. All models fail within 5 to 6 turns without retries. Test feedback gives up to 12x more turns. For one model, harnesses differ up to 6x. | Python by default; ablations in JavaScript and Rust. The ground truth is a Flask server. | Generated pytest over HTTP against the server in Docker, compared to a reference schema state. The tests are always made without an LLM. Default 2 retries per turn; feedback from detailed to binary. | Passed turns; token totals (Limitations section); prices and costs (Appendix A, Tables 5 and 6). | Low: an agent image with our toolchain and a spec line. | Code CC BY-NC 4.0; paper CC BY-NC-SA 4.0 | [R](https://arxiv.org/abs/2606.19613) [R](https://github.com/amazon-science/StaminaBench) |
| AutoBaxBench / AutoBaxBuilder | v1 2025-12-24, v2 2026-05-21; ICML 2026 | Correct and secure backends on 40 generated scenarios (10 easy, 20 medium, 10 hard) for 14 frameworks. An LLM pipeline writes the spec, the tests, and the exploits. Claude-4.5 Sonnet: pass@1 82.7%, sec_pass@1 36% (25% on hard). | Go, JavaScript, PHP, Python, Ruby, Rust (the BaxBench Envs) | Functional tests and end-to-end exploits over REST: "programming-language and backend-framework-agnostic". | Only for construction: under USD 160 in total, USD 3.9 per scenario. | Low: one BaxBench Env. The generator sets the size with -d 1, 3, or 5 endpoints. Take the scenarios from the repo (src/scenarios) to match v2. | MIT (code and data) | [R](https://arxiv.org/abs/2512.21132) [R](https://github.com/eth-sri/AutoBaxBuilder) [R](https://huggingface.co/datasets/eth-sri/AutoBaxBench) |
| BaxBench | v1 2025-02-17, v3 2025-05-30; ICML 2025; release v1.0.0 2025-09-15; repo push 2026-01-30 | Correct and secure backends: 28 scenarios for 14 frameworks = 392 tasks. Single-shot, with no repair loop. 62% of the solutions of the best model are incorrect or insecure. | Go (Fiber, Gin, net/http), JavaScript (Express, Fastify, Koa, Nest), PHP (Lumen), Python (aiohttp, Django, FastAPI, Flask), Ruby (Rails), Rust (Actix) | HTTP functional tests and exploits for 13 CWEs. Some checks read the SQLite file at the path that the prompt fixes (./db.sqlite3). | None. | Low: one Env dataclass in src/env (Dockerfile, manifest, entrypoint, port 5000, SQLite path), registered in all_envs. | MIT (code and data) | [R](https://arxiv.org/abs/2502.11844) [R](https://github.com/logic-star-ai/baxbench) [R](https://baxbench.com) |
| ABC-Bench | v1 2026-01-16; Findings of ACL 2026 | The full backend lifecycle in a real repo: explore, implement, configure, deploy, and pass API tests. 224 tasks from 127 MIT repos; 92 tasks need environment setup. Claude Sonnet 4.5 63.2%; most open models 0.0% on Rust. | C# 43, JavaScript 38, Java 34, Ruby 33, PHP 33, Go 29, Python 10, Rust 4 | run-tests.sh: an "HTTP-level validator driven by pytest" that runs outside the container. | Turns (more than 60 for strong models) and six error classes. No tokens. | High for the tasks, because they edit repos in other languages. Low for the validators if we re-specify a task as greenfield. | Data ODC-BY; GitHub code has no licence file | [R](https://arxiv.org/abs/2601.11077) [R](https://aclanthology.org/2026.findings-acl.1142/) [R](https://huggingface.co/datasets/OpenMOSS-Team/ABC-Bench) |
| Constraint Decay | v1 2026-05-07, v2 2026-09-18; COLM 2026 | Correctness when structural rules (layers, a database, an ORM) are added in four levels, L0 to L3. 100 tasks on the RealWorld Conduit API (19 endpoints). About 27 points are lost from L0 to L3. Best L3: 78.6% of assertions but 8.3% pass@1. About 48% of logic errors are data-layer defects. | Python 3.12 (4 frameworks), Node.js 20 (4 frameworks) | Newman runs a Postman collection (32 requests, 291 assertions). Static verifiers read the diff; a violation sets the score to zero. | Mean tokens per run (Tables 12 and 13); 3.73B input and 42.7M output tokens in total. | Low for the HTTP oracle. The verifier rules must be written again for the new language. | Repo has no licence file; RealWorld spec MIT | [R](https://arxiv.org/abs/2605.06445) [R](https://github.com/francdente/constraint-decay) [R](https://github.com/realworld-apps/realworld) |
| RepoGenesis | v1 2026-01-20, v3 2026-04-15; ACL 2026 Main | A microservice repo from a README: Pass@1, API Coverage, and Deployment Success Rate. 106 repos, 1,258 endpoints, 2,335 tests; 30 repos are public. Best Pass@1: 23.67% (Python), 21.45% (Java). | Python 60, Java 46 | Tied to the language. Python tests import the app (FastAPI TestClient). Java tests start the app in-process and then send HTTP. | None found. | High: port the tests to HTTP clients first. | MIT | [R](https://arxiv.org/abs/2601.13943) [R](https://github.com/microsoft/DKI_LLM/tree/main/RepoGenesis) |
| Encore ai-backend-benchmark | repo 2026-04-24 (one commit); blog 2026-05-20 | Claude Code builds TypeScript backends on 5 frameworks. 3 tasks: an orders API; a pub/sub event and a daily scheduled job; trace propagation. A framework vendor runs it. The blog runs the tasks in sequence, but the README starts each task from a clean starter. | TypeScript | 31 vitest HTTP tests, a typecheck test for t1, and 5 production-readiness checks in run 3. | README: pass rate, turns to green, token cost, and wall clock for each cell. The blog gives turns and USD, not tokens. | Medium: a starter and an exe.dev VM setup. | No licence file (all rights reserved) | [R](https://github.com/encoredev/ai-backend-benchmark) [R](https://encore.dev/blog/ai-benchmark) |
| EvoCode-Bench | v1 2026-05-22 ("Work in Progress"); results re-released 2026-06-20, updated 2026-06-25 | An agent keeps a workspace correct over 5 to 15 rounds of changed requirements. 26 tasks, 227 rounds. Current table (one attempt): Claude-Opus-4.8 59.1, GPT-5.5 29.5. The authors call each number before 2026-06-20 outdated: a verifier leak, one contaminated task, and 11 task defects. | Mixed, for example a Go CLI | Cumulative executable tests after each round. The current format is the Harbor official multi-step format (steps in task.toml). The paper metrics MT@4 and SR are now legacy. | Average turns and output tokens for each agent; 24.4B tokens in total. | Medium: re-specify the tasks; the protocol is reusable. | Code MIT; data CC BY-NC 4.0 | [R](https://arxiv.org/abs/2605.24110) [R](https://github.com/UniPat-AI/EvoCodeBench) [R](https://huggingface.co/datasets/UnipatAI/EvoCodeBench) |
| Vibe Code Bench (Vals AI) | first release 2025-11; arXiv v3 2026-05-13; leaderboard v1.1 2026-11-18 | Full web apps from a spec: 100 specs (50 held out), 964 browser workflows. Use it only for its report layout. | Free choice | A browser agent. Step-level agreement between evaluators is only 31.8% to 93.6%. | Score, Cost/Test, Tokens/Test, and Duration/Test for each model and harness. | High: a UI oracle and private specs. | Paper CC BY 4.0; no code | [R](https://www.vals.ai/benchmarks/vibe-code) [R](https://arxiv.org/abs/2603.04601) |

### 3.2 Multi-language and new-language task sets

| Name | Date | What it measures | Languages | Oracle | Token reporting | Effort | Licence | Source |
|---|---|---|---|---|---|---|---|---|
| Multi-LCB | ICLR 2026; arXiv v1 2026-06-18 | Single-turn Pass@1 on the same LiveCodeBench tasks in 12 languages; 24 LLMs, 10 runs at temperature 0.2. Python mean 0.482; Java and C++ about 0.44; Scala below 0.29. | C++, C#, Python, Java, Rust, Go, TypeScript, JavaScript, Ruby, PHP, Kotlin, Scala | Hidden I/O tests in a sandbox for each language (6 s, 4 GB, no network). A release-date filter controls contamination. | None. | Low to medium: replace the header of the code block and add a compile and run profile. | Repo MIT; benchmark data CC BY-NC 4.0 | [R](https://arxiv.org/abs/2606.20517) [R](https://github.com/Multi-LCB/Multi-LCB) |
| Agnostics (Ag-LiveCodeBench-X) | v1 2025-08-06, v4 2026-08-31; ICLR 2026 | Code judged "solely by its externally observable behavior". An LLM rewrites unit-test tasks into I/O tasks. | Lua, Julia, R, OCaml, Fortran, and others | I/O tests. A short YAML profile for each language tells the verifier how to compile and run. | None. | Very low: "a small (often 4-line!) configuration". | Repo has no licence file | [R](https://arxiv.org/abs/2508.04865) [R](https://github.com/nuprl/agnostics-framework) [R](http://abgru.me/project/agnostics) |
| EsoLang-Bench | v1 2026-03-10, v2 2026-05-11; NeurIPS 2026 poster | The same 80 problems in esoteric languages and in Python and JavaScript. Full docs in the prompt; 5 prompt regimes. Python and JavaScript reach 100%. The best esoteric score is 11.2%. Few-shot adds 0.8 points (Wilcoxon p = 0.505). | Brainfuck, Befunge-98, Whitespace, Unlambda, Shakespeare; Python, JavaScript | 6 hidden stdin/stdout tests, stored once for each problem and never in the prompt. All 6 must pass. Failures split into compile, runtime, and logic errors. | Token caps only. | Low: an interpreter and a docs file for the language. No new tests. | Code MIT; data CC BY 4.0 | [R](https://arxiv.org/abs/2603.09678) [R](https://github.com/Lossfunk/EsolangBench) |
| CangjieBench | v1 2026-03-15, v2 2026-08-12; ESEM 2026 | Pass@1 and compile rate in Cangjie, a language that is almost absent from training data. Five methods: Direct, Syntax-Constrained (reference in the prompt), RAG over code, RAG over docs, and Agent (Codex CLI 0.63.0, Qwen Code 0.2.3, iFlow 0.4.8). The 2,146-token reference raises GPT-5 Pass@1 (text to code) from 4.8% to 50.4%. Codex CLI with GPT-5 reaches 66.9%. | Cangjie | Compile, then the unit tests. ClassEval tasks add an integration test. | Input plus output tokens for each task and method, all agent turns included. Direct uses about 1k; agents use 10x to 120x more. | Medium: translate 248 tasks by hand. | MIT; includes CangjieBench-harbor, 248 Harbor tasks | [R](https://arxiv.org/abs/2603.14501) [R](https://arxiv.org/html/2603.14501) [R](https://github.com/cjhCoder7/CangjieBench) |
| No Resource, No Benchmarks, No Problem? | v1 2026-06-15; IEEE TSE | pass@1 in two no-resource languages against low- and high-resource languages on the same tasks. Zero-shot, few-shot, RAG, and more pre-training. Zero-shot McEval-Hard: 0% to 1% for the no-resource languages, 59.3% to 88.9% for the high-resource languages (GPT-4o, o3-mini). About two thirds of GPT-4o failures are syntactic. | Gleam, MoonBit; Racket, Julia, Haskell, Lua, R; Java, Python | Translated unit tests; 10 runs for each task. McNemar test, Benjamini-Hochberg correction, odds ratios. It keeps only the tasks that exist in all languages. | None at inference. | Medium: a MultiPL-E translator, a ChatGPT draft, and a review by a language expert. | Paper and replication package CC BY 4.0 | [R](https://arxiv.org/abs/2606.16827) [R](https://doi.org/10.5281/zenodo.19366887) |
| AlgoVeri | v1 2026-02-10, v2 2026-06-03; ICML 2026 | Verified code for 77 classical algorithms with "identical functional contracts" in each language. Gemini-3 Flash: Dafny 40.3%, Verus 24.7%, Lean 7.8%. It replaces vericoding (arXiv 2509.22908) for aligned comparisons. | Dafny, Verus, Lean 4 | The verifier of each language checks the program against the contract. The toolchain versions are pinned. | None. | Medium: write the 77 contracts and a checker image. | Apache-2.0 | [R](https://arxiv.org/abs/2602.09464) [R](https://github.com/haoyuzhao123/algoveri) |
| AutoCodeBench and AutoCodeBench-V2 | v1 2025-08-12; V2 2025-12-04, data fix 2026-02-17; ICLR 2026 | Pass@1 on generated problems in 20 languages. Multi-turn repair with sandbox feedback: DeepSeek-V3-0324 goes from 48.1% to 59.7% in 3 turns. | 20 languages | Sandbox execution; the expected outputs come from the reference solution. | None. | High for a paired claim: the problems differ between languages. Reuse the sandbox image (more than 30 languages) and the 3-turn protocol. | Apache-2.0 | [R](https://arxiv.org/abs/2508.09101) [R](https://github.com/Tencent-Hunyuan/AutoCodeBenchmark) |
| MultiPL-E | paper 2022-08; repo push 2026-04-12 | HumanEval and MBPP, translated by small compilers into 24 languages. Multi-LCB and Ag-LiveCodeBench-X replace it as task sets. Keep it for the translator method. | 24 languages, Rust, Go, TypeScript, and Java included | Translated unit tests. Result classes: OK, syntax error, exception, timeout. | None. | Documented: a Translator class (38 to 479 lines), an eval script, a Dockerfile, and a terms.csv row. | Repo: BSD 3-Clause with a machine-learning-training restriction. HF data: MIT. | [R](https://github.com/nuprl/MultiPL-E) [R](https://github.com/nuprl/MultiPL-E/blob/main/LICENSE) [R](https://huggingface.co/datasets/nuprl/MultiPL-E) |
| Aider Polyglot | 2024-12-21; last entry 2025-10-03 | Edit Exercism exercises until the unit tests pass, in two tries. 225 exercises. It is saturated: the top pass_rate_2 is 88.0. LiveRepoReflection (arXiv 2507.09866) is a less contaminated set of the same kind. | C++, Go, Java, JavaScript, Python, Rust | Exercism unit tests. Try 2 sees the test output, which is one repair round. | Run totals: cost, prompt, completion, and thinking tokens. Counters for malformed responses, syntax errors, indentation errors, test timeouts, and context exhaustion. | Medium to high: port each exercise. | aider Apache-2.0; the exercise repo has no licence file | [R](https://aider.chat/2024/12/21/polyglot.html) [R](https://raw.githubusercontent.com/Aider-AI/aider/main/aider/website/_data/polyglot_leaderboard.yml) [R](https://arxiv.org/abs/2507.09866) |
| Zero (zerolang) evals | repo 2026-05-15; v0.3.4 2026-06-13; push 2026-09-16 | Claude agents write programs in Zero, a new language for agents. They learn it only from a skill document and the JSON diagnostics of the compiler. The project publishes no comparison with other languages. | Zero | Check, run, and compare stdout, plus source-shape checks. 53 Rosetta Code tasks; CLI tasks and a CRM HTTP API package. | Usage for each step, turns, tool calls, check calls, run calls. Budget: 30 turns. | Not applicable. To reuse the runner, replace the Zero check and run commands with ours. | Apache-2.0 | [R](https://github.com/vercel-labs/zerolang) [R](https://github.com/vercel-labs/zerolang/blob/main/evals/README.md) [R](https://github.com/vercel-labs/zerolang/blob/main/evals/src/run.ts) |

### 3.3 Harnesses and agents

| Name | Date | What it does | Languages | Oracle | Token reporting | Effort | Licence | Source |
|---|---|---|---|---|---|---|---|---|
| Harbor | repo 2025-08-04; v0.26.0 2026-11-13 | Runs an agent (Claude Code, Codex CLI, OpenHands, mini-swe-agent, and others) on container tasks. The official harness of Terminal-Bench (now 4.1). Adapters exist for aider_polyglot, swebench, swebench_multilingual, and multi-swe-bench. | Any | tests/test.sh writes reward.txt, or reward.json for multi-dimensional rewards. | For each trial: n_input_tokens (cache included), n_cache_tokens, n_output_tokens, cost_usd, model_usage. The ATIF trajectory has steps, tool calls, and metrics. There is no separate field for reasoning tokens. | Low: a Docker image with the toolchain. | Apache-2.0 | [R](https://github.com/harbor-framework/harbor) [R](https://raw.githubusercontent.com/harbor-framework/harbor/main/src/harbor/models/agent/context.py) [R](https://docs.harborframework.com/agents/atif) |
| Inspect AI | PyPI 0.0.1 2024-04-03; 0.3.291 2026-11-17 | A general eval framework: one sandbox for each sample, epochs with reducers, and logs that load into dataframes. | Any | A scorer that we write; multi-value scores are possible. | For each sample: total_tokens, model_usage, turn_count, message_count, working_time, retries. Tool calls are in messages_df. | Low to medium: a Dockerfile, a solver, and a scorer. Built in: clustered stderr, a pass_at_k reducer, token_limit (output tokens only, as an option), and cost_limit. | MIT | [R](https://pypi.org/project/inspect-ai/) [R](https://inspect.aisi.org.uk/dataframe.html) [R](https://inspect.aisi.org.uk/metrics.html) [R](https://inspect.aisi.org.uk/setting-limits.html) |
| mini-swe-agent | repo 2025-06-28; v2.4.6 2026-07-23 | A minimal agent with bash only. Tokenmaxxing, BackendForge, and all runs of the SWE-bench Multilingual leaderboard use it. | Any | None of its own. | instance_cost, api_calls, and cost for each call. The token counts are in the stored raw response of each message. | Low. | MIT | [R](https://github.com/SWE-agent/mini-swe-agent) [R](https://raw.githubusercontent.com/SWE-agent/mini-swe-agent/main/docs/usage/output_files.md) |
| SWE-bench family (SWE-bench, SWE-bench Multilingual, Multi-SWE-bench) | swebench 5.0.2 2026-08-18; Multilingual 2025-04-29; Multi-SWE-bench 2025-04, NeurIPS 2025 | Issue resolution in real repos. ProgramBench (arXiv 2605.03546, 2026-05) is newer, from the SWE-bench team: hidden behavioural tests, and the agent chooses the language. | Multilingual: C, C++, Go, Java, JavaScript, TypeScript, PHP, Ruby, Rust. Multi-SWE-bench: Java, TypeScript, JavaScript, Go, Rust, C, C++. | FAIL_TO_PASS and PASS_TO_PASS tests. | Multi-SWE-bench: tokens (Table 7) and cost (Table 8) for each language. Multilingual board: cost per instance. | Not possible: it needs real repos with history. | SWE-bench and Multilingual MIT; Multi-SWE-bench Apache-2.0 | [R](https://github.com/SWE-bench/SWE-bench) [R](https://www.swebench.com/multilingual.html) [R](https://arxiv.org/abs/2504.02605) [R](https://arxiv.org/abs/2605.03546) |

### 3.4 Studies and methods for tokens and errors

| Name | Date | What it measures | Languages | Oracle | Token reporting | Effort | Licence | Source |
|---|---|---|---|---|---|---|---|---|
| The Best Programming Language for Tokenmaxxing (Wu, Anderson, Guha) | v1 2026-07-24, v2 2026-10-21; LMPL 2026 | The output tokens of an agent for the same problem in different languages, with control for problem difficulty. 100 MiniLCB problems, 4 languages, 5 models: 2,000 sessions. Against Python: OCaml 1.28x to 1.69x (p < 0.001), Rust 1.07x to 1.57x, Java 0.85x (Gemma, not significant) to 1.34x. For GPT-5.5 and Claude-Sonnet-4.6, all three languages cost more than Python. ICC 0.73 to 0.97. 92% of the failed Gemma snapshots in OCaml are compile errors. Agents revise code that already passes, and they prototype in Python. | Python, Java, Rust, OCaml | Visible stdin/stdout tests through test.sh: 2 to 45 for each task, 10 s each. | Main metric: output tokens over the trajectory, reasoning included. Tokens per success: all output tokens, failed runs included, divided by the solved trajectories. Tokens and turns before and after the first pass (Table 3). Median input tokens, reasoning tokens, and wall clock (Table 17). | Low: a container with a preconfigured toolchain and test.sh. | Paper CC BY 4.0. Code and data are not released ("upon publication"). | [R](https://arxiv.org/abs/2607.22807) [R](https://arxiv.org/html/2607.22807v2) [R](https://conf.researchr.org/home/splash-issta-2026/lmpl-2026) |
| Frontier Coding Agents Use Metaprogramming to Adapt to Unfamiliar Programming Languages | v1 2026-06-09; NeurIPS 2026 poster | How coding agents solve tasks in esoteric languages. Mean accuracy over four languages: GPT-5.4 xhigh 99.7%, Opus 4.6 86.9%, Sonnet 4.6 66.3%, Haiku 4.5 24.7%. Opus 4.6 solves 64/80 Brainfuck problems with Python generators. A ban on generators "causes large performance drops". | Brainfuck, Befunge-98, Whitespace, Shakespeare | Up to 3 hidden submissions with 6 hidden tests. The agent gets only the count of passed tests. | Output tokens only for the Claude agents, on the first 20 Brainfuck and Befunge-98 problems. | Low: an interpreter and one system prompt for the language. | Paper CC BY 4.0. The harness is only in an anonymous supplement. | [R](https://arxiv.org/abs/2606.10933) [R](https://neurips.cc/virtual/2026/poster/152963) |
| Programming Language Confusion (PLC) | v1 2025-03-17, v2 2026-02-02; SANER 2026 | How often a model writes the wrong language, and which language it drifts to. About 75k samples, 10 LLMs. Python is the main attractor. C# and C++ drift to Java; PHP and TypeScript drift to JavaScript. Explicit language keywords in the prompt help most. Metrics: LCPR (share in the target language), CPPR (share that parses in the detected language), DMR (share of drifted samples that go to one language). FPR (passes at least one test) is reported apart. | 16 languages | A detector ensemble (98.2% accuracy), Tree-sitter, and unit tests. | None. | Low for the metrics. Our parser gives CPPR. Rules on our parse errors name the foreign construct, because the detectors do not know the new language [A]. | Paper CC BY-NC-SA 4.0; repo has no licence file | [R](https://arxiv.org/abs/2503.13620) [R](https://github.com/TruX-DTF/PLC) |
| Unreliable in Practice? A Comprehensive Study of Errors in LLM-Generated Code | v1 2026-08-01; ISSRE 2026 | A taxonomy of the compile and runtime errors in 86,726 failed samples from 7 LLMs: 15 compile labels and 16 runtime labels. The top compile error is "Missing import" for C and C++, and "Incompatible parameter types" for Java and Rust. It has no habit class. | C++, Java, C, Rust | Compiler and run. GPT-4.1-mini labels each failure (accuracy 0.84 to 0.91 on compile errors). | None. | Medium: add labels for the new language. | Paper CC BY 4.0; code URL not verified | [R](https://arxiv.org/abs/2608.00661) |
| Bridging the Knowledge Void (ILA-agent) | v1 2026-01-16 | An agent learns an unfamiliar language at inference time with tools: doc search, structure views, execution, and type lookup. Claude-Sonnet-4.5 reaches 81.94. In the ablation for Qwen3-Max (73.55), no verification gives 53.55, no semantic search 53.55, no type lookup 57.42. | Cangjie (target), Java (source for translation) | Private tests; compile rate apart. | 15 turns, 128K context; no tokens. | Medium: index the reference document and add the tools. | Paper CC BY 4.0; benchmark not released | [R](https://arxiv.org/abs/2602.06976) |
| Anka | v1 2025-12-29 (single author) | A DSL for LLMs against Python with pandas on 100 data tasks. Claude 3.5 Haiku: 95.8% against 91.2%; multi-step 100% against 60%. Only the Anka arm gets a guide (about 100 lines). It has no tokens and no statistics. | Anka, Python | Expected output. A task passes when at least 50% of 10 samples pass. | None. | Not applicable. | MIT | [R](https://arxiv.org/abs/2512.23214) [R](https://github.com/BleBlo/Anka) |
| How Do AI Agents Spend Your Money? (Bai et al.) | v1 2026-04-24, v3 2026-10-02; NeurIPS 2026 workshop | Token use of 8 LLMs with OpenHands on SWE-bench Verified. Runs on one task differ up to 30x in total tokens. Input tokens, not output tokens, drive the cost. More tokens do not give more accuracy. A related newer paper measures removable token spans (arXiv 2611.07238). | Python | SWE-bench tests | Input and output tokens for each trajectory. | Not applicable. | arXiv paper; no code linked | [R](https://arxiv.org/abs/2604.22750) [R](https://arxiv.org/abs/2611.07238) |
| Is Self-Repair a Silver Bullet? (pass@t) and 2026 repair studies | v5 2024-02 (ICLR 2024); 2026-04; 2026-07 | pass@t: the pass rate against all sampled tokens, feedback and repair included. Repair gains are "often modest" at equal cost. 2026: most gains come in the first two rounds (2604.10508). "The first three to four repair iterations account for most achievable gains", and the feedback design matters more than the model (2607.05197). | Python | Unit tests | Tokens are the x-axis of the metric. | None: the metric is language-agnostic. | Repo archived, no licence file | [R](https://arxiv.org/abs/2306.09896) [R](https://arxiv.org/abs/2604.10508) [R](https://arxiv.org/abs/2607.05197) |
| SWE-Effi | v1 2025-09-11, v2 2025-09-18 | Effectiveness under a budget: the normalized area under the curve of resolve rate against tokens (EuTB, cap 2M tokens per issue), USD (EuCB, cap USD 1), CPU time, and inference time. "Expensive failures": failed runs use more tokens than solved runs. | Python | SWE-bench tests | Tokens, USD, and time for each run. | Not applicable. | Paper CC BY-NC-ND 4.0; repo licence "Other"; the eval script is not released | [R](https://arxiv.org/abs/2509.09853) [R](https://github.com/Centre-for-Software-Excellence/SWE-Effi) |
| How does programming language affect token efficiency and correctness? (Dan Luu) | 2026-08 | Correctness, cost, and time by language. Task 1: a zstd decoder from the RFC, about 40 runs for each language and effort level, no internet. Task 2: a Pandoc rebuild on ProgramBench. Clojure fails 36/40 at medium effort and 5/40 at ultra effort. The language ranking changes with the effort level. Popular languages tend to be more correct and cheaper. | A broad set of static and dynamic languages | Hidden or holdout behavioural tests. Agents wrote them; the author did not audit all of them. | Cost and wall clock; no token split. | Not reusable: no code is published. | Blog post | [R](https://danluu.com/pl-tokens/) |
| ai-coding-lang-bench (Yusuke Endoh) | 2026-03-04 to 2026-03-05 | Claude Code (Opus 4.6) builds and then extends a mini-git: 15 configurations, 2 phases, 20 trials. One test runs a wrong path, and a later Go agent made a symlink from that path to its own binary. Thus the per-language failure counts are not valid. Dan Luu and Tokenmaxxing replace it. | 13 languages, plus Python with mypy and Ruby with Steep | Black-box shell tests. | For each run: input, output, cache-write, and cache-read tokens, USD, turns, duration (from claude -p with JSON output). | Low. | No licence file | [R](https://github.com/mame/ai-coding-lang-bench) [R](https://danluu.com/pl-tokens/) |
| LangSelect (MultiLang-Bench) | v1 submitted 2026-07-15 | The token length of verified solutions to the same task in 8 languages. A router charges every attempt, failures and fallbacks included. | C, Clojure, Go, Java, Julia, Python, Ruby, Rust | Unit tests | Generated-code tokens only (tiktoken cl100k_base). No prompt or reasoning tokens. | Unknown. | Paper CC BY 4.0. The artifact link returns HTTP 410. | [R](https://arxiv.org/abs/2609.18959) |
| Tokka-Bench | v1 2026-03-25 | Tokenizer fit of 7 BPE tokenizers on 100 natural and 20 programming languages: bytes per token, fertility, and other metrics. Programming-language efficiency "has converged among recent tokenizers". | 20 programming languages | Static measurement. | Static token statistics. | Low: a text corpus of the new language. | No LICENSE file (the README intends MIT) | [R](https://arxiv.org/abs/2610.08794) [R](https://github.com/bgub/tokka-bench) |
| Token Sugar; The Hidden Cost of Readability; SimPy | 2025-12 (ASE'25); 2025-08 (ICSE'26); 2024 (ISSTA'24) | Token savings from a changed syntax or from removed formatting. Hidden Cost: the removal of formatting cuts input tokens by 24.5% on average, with stable accuracy. Token Sugar: up to 15.1% fewer source tokens. SimPy: 10.4% to 13.5% fewer tokens. Token Sugar complements SimPy; it does not replace it. | Python; Hidden Cost also Java, C++, C# | Pass@1 and fill-in-the-middle accuracy | Static and generated token counts; no agent loop. | Low for static counts. | Token Sugar and SimPy repos have no licence file | [R](https://arxiv.org/abs/2512.08266) [R](https://arxiv.org/abs/2508.13666) [R](https://arxiv.org/abs/2404.16333) |

### 3.5 Leaderboards for baseline numbers and the report layout

| Name | Date | What it shows | Languages | Oracle | Token reporting | Effort | Licence | Source |
|---|---|---|---|---|---|---|---|---|
| SWE-rebench (V2 and the multi-language leaderboard) | V2 paper 2026-02-27, v2 2026-06-01 (ICML 2026); leaderboard window 2026-05-15 to 2026-07-01 | Fresh issue tasks: 111 tasks from 65 repos, 5 runs for each model and task. Best Pass@1 for each language: Rust 68.0, Go 74.3, TypeScript 78.3, Python 57.0, Java 60.0 (shared scaffold). | Go 21, Java 21, Python 20, Rust 25, TypeScript 24 tasks | FAIL_TO_PASS and PASS_TO_PASS | Pass@1 ± SE, Pass@5, "Pass all 5", cost and tokens per problem with the cached share. | Not possible. | V2 data CC-BY-4.0 | [R](https://swe-rebench.com) [R](https://teletype.in/@ibragim_bad/swe-rebench-2026-07) [R](https://arxiv.org/abs/2602.23866) |
| Artificial Analysis Coding Agent Index v2.1 | 2026-11 | Three benchmarks with equal weight, 3 attempts for each task. It averages the attempts for each task, then averages over tasks. | No split by language | The oracles of the components | For each task: input, cache, cache-write, reasoning, and output tokens. Cost from provider token counts and live cache-hit rates. | Not applicable. | Proprietary method | [R](https://artificialanalysis.ai/methodology/coding-agents-benchmarking) |
| Terminal-Bench 4.1 leaderboard | entries to 2026-11-17 | Resolution rate ± 95% CI, total tokens, and total cost for each agent and model. | Any | Task test scripts | Totals for each run. | Not applicable. | Not stated | [R](https://www.tbench.ai/leaderboard) |

### 3.6 Statistics methods

| Name | Date | What it gives | Use for us | Code | Source |
|---|---|---|---|---|---|
| Miller, "Adding Error Bars to Evals" | 2024-11 | The paired SE, the clustered SE (up to about 3x the naive SE), the variance of K samples for each question, and a sample-size formula (Eq. 9). His example of n = 969 sets the within-question noise to zero. He concludes that new evals need at least 1,000 questions. | The paired SE on per-task differences, clustered by task family. | Not needed. | [R](https://arxiv.org/abs/2411.00640) |
| Wang, "Measuring all the noises of LLM Evals" | v1 2025-12-24, v3 2026-10-13 | It splits the paired variance into data noise and prediction noise: "paired prediction noise typically exceeds paired data noise". Appendix A.2 gives a small-K correction. | Decide the number of runs for each task. | Formulas and an interactive tool | [R](https://arxiv.org/abs/2512.21326) [R](https://all-the-noises.github.io) |
| Mandujano Reyes, multiple model comparison | v1 2026-08-23, v2 2026-10-18 | A random-effects model for K systems on shared items. It equals Miller for K = 2. It uses Tukey for balanced designs. A Tukey adjustment through emmeans in mixed or unbalanced models is only approximate. | Six arms. | No release found. | [R](https://arxiv.org/abs/2608.22659) |
| Kotawala, "Resolution Diagnostics for Paired LLM Evaluation" | 2026-05-28 | q = N/N* at alpha 0.05 and power 0.8. The shortcut "Cohen's h times (1 − rho)" is wrong by about 2x in close comparisons; G*Power and R pwr have this error. | The power plan before the main run. | None. | [R](https://arxiv.org/abs/2605.30315) |
| Hardy et al., "More Tasks Won't (Always) Fix An Agent Leaderboard" | 2026-09-30 | Reliability is 0.935 to 0.994 for model-scaffold systems, but 0.148 to 0.841 for the models. Infinitely many similar tasks add at most 0.097. | Use two scaffolds for a claim about the language. | None. | [R](https://arxiv.org/abs/2610.00651) |
| Vats and Golev, "The Scaffold Effect in Coding Agents" | 2026-06-08 (under review) | The harness alone changes tokens per solved task by up to 40x. Pass-rate gaps are 0 to 8 points. Failure fingerprints: REASON, VERIFY/MAX_TURNS, idle loop, TIME. | Pin one harness version in all arms. | Configs, logs, and scripts released; licence not stated. | [R](https://arxiv.org/abs/2607.22585) |
| Bowyer et al.; Hariri et al. ("Don't Pass@k") | 2025-03 (ICML 2025); 2025-10, v4 2026-05 (ICLR 2026) | CLT error bars are too narrow below a few hundred items. Bayesian alternatives, and Dirichlet posteriors in place of pass@k. | Small subsets: the pilot, one task family, one error class. | bayes_evals (MIT), scorio (MIT) | [R](https://arxiv.org/abs/2503.01747) [R](https://arxiv.org/abs/2510.04265) [R](https://github.com/sambowyer/bayes_evals) [R](https://github.com/mohsenhariri/scorio) |

## 4. Backend task sources with a language-agnostic oracle

| Source | Size | Oracle | How we reuse it [A] | Licence | Caveat |
|---|---|---|---|---|---|
| BaxBench | 28 scenarios, 54 endpoints | HTTP tests and exploits against a container on port 5000 [R](https://github.com/logic-star-ai/baxbench) | Add the new language and each baseline framework as an Env. Wrap each scenario as a Harbor task with our agent loop and token log. | MIT | Single-shot by design. The security checks read SQLite at ./db.sqlite3 [R](https://github.com/logic-star-ai/baxbench). The new language needs an adapter for these checks, or we drop them [A]. |
| AutoBaxBench and AutoBaxBuilder | 40 scenarios, and a generator for more | HTTP tests and exploits [R](https://arxiv.org/abs/2512.21132) | Generate fresh scenarios at a set difficulty, so that no arm saw them in training. A person checks each scenario. | MIT | The tests come from an LLM, so they need a review. |
| BackendForge | 56 tasks, 2,345 operations, 7,839 final tests | Hidden HTTP pytest at four cumulative levels; mock services [R](https://github.com/PKU-ASE-RISE/BackendForge) | Use it as the newest held-out backend set. Copy its task format for our own tasks. | Apache-2.0 | Large tasks: USD 3.39 to 5.55 per task for frontier models [R](https://arxiv.org/abs/2607.11042). |
| StaminaBench | 20 scenarios with 100 turns; an offline generator | Generated HTTP pytest against a reference state [R](https://github.com/amazon-science/StaminaBench) | An arm where the service changes over time, with repair rounds in each turn. | CC BY-NC 4.0 | Non-commercial licence. |
| RealWorld Conduit | 19 endpoints | An OpenAPI spec with Hurl and Bruno suites [R](https://github.com/realworld-apps/realworld); the Postman collection in the Constraint Decay repo [R](https://github.com/francdente/constraint-decay) | A small, well-known spec. Add rule levels as Constraint Decay does. | Spec MIT; Constraint Decay repo has no licence file | Many public implementations exist, so it is contaminated for the baseline languages [A]. The Postman file that the docs link is no longer in the tree [R](https://github.com/realworld-apps/realworld). |
| ABC-Bench validators | 224 tasks | pytest HTTP validators that run outside the container [R](https://huggingface.co/datasets/OpenMOSS-Team/ABC-Bench) | Re-specify selected tasks as greenfield specs and keep the validators. | Data ODC-BY | The tasks edit real repos in other languages, so each spec needs a rewrite. |
| RepoGenesis specs | 30 public repos | In-process tests [R](https://github.com/microsoft/DKI_LLM/tree/main/RepoGenesis) | Reuse the README specs and the metrics API Coverage and Deployment Success Rate. Port the tests to HTTP. | MIT | The test port costs effort. |
| Encore tasks | 3 tasks | vitest HTTP tests [R](https://github.com/encoredev/ai-backend-benchmark) | Seeds for a task family with events and schedules (t2: a pub/sub event and a daily job). | No licence file | Ask the owner before reuse. Vendor bias. |
| EvoCode-Bench protocol | 26 tasks, 227 rounds | Cumulative tests for each step, in the Harbor multi-step format [R](https://github.com/UniPat-AI/EvoCodeBench) | Copy the protocol, not the tasks. | Code MIT; data CC BY-NC 4.0 | Not specific to backends. |

Control set outside backends [A]: stdin/stdout tasks from Multi-LCB, Ag-LiveCodeBench-X, or EsoLang-Bench. They separate a general language effect from a backend effect. The Tokenmaxxing study uses this setting, so our control numbers can be compared with its numbers [R](https://arxiv.org/abs/2607.22807).

Gap: durable machines. The sweep found no benchmark for durable logs, timers, retries with backoff, or exactly-once outputs [A]. The closest seeds are Encore t2 (a pub/sub event and a scheduled job) [R](https://encore.dev/blog/ai-benchmark) and the guards and cascade deletes of StaminaBench [R](https://arxiv.org/abs/2606.19613). Proposal [A]:

1. Write a task family for durable machines in the BackendForge format: spec.md, openapi.yaml, a Dockerfile, and hidden HTTP tests.
2. Give the oracle a test clock and fault injection through one fixed HTTP interface. Every arm implements the same interface.
3. Write one contract for each task. Express the contract in each language, as AlgoVeri does [R](https://arxiv.org/abs/2602.09464).
4. Generate variants with a pipeline like AutoBaxBuilder. A person checks each variant.

## 5. Measurement of tokens and errors

### 5.1 How the best work measures tokens

| Source | Token unit | Failed runs | Other |
|---|---|---|---|
| Tokenmaxxing [R](https://arxiv.org/abs/2607.22807) | Output tokens over the full trajectory, reasoning included. | Included. Tokens per success = all output tokens / solved trajectories. | Tokens and turns before and after the first pass. Median input and reasoning tokens. LMM on log tokens. |
| BackendForge [R](https://arxiv.org/abs/2607.11042) | Output tokens and USD for each task. | Included in the task average. | Two oracle strengths next to the tokens. |
| SWE-rebench [R](https://teletype.in/@ibragim_bad/swe-rebench-2026-07) | Tokens for each problem with the cached share; USD with cache-read and cache-write prices. | Five runs for each pair. | Pass@1 ± SE, Pass@5, Pass all 5. |
| Artificial Analysis [R](https://artificialanalysis.ai/methodology/coding-agents-benchmarking) | Input, cache, cache-write, reasoning, and output tokens for each task; USD. | Three attempts averaged for each task, then over tasks. | Each task has equal weight. |
| Harbor [R](https://raw.githubusercontent.com/harbor-framework/harbor/main/src/harbor/models/agent/context.py) | Input (cache included), cache, and output tokens; USD for each trial. | Each trial. | Usage for each model, subagents included. |
| CangjieBench [R](https://arxiv.org/abs/2603.14501) | Input plus output, summed over all agent turns. | Each task. | It states the length of the reference: 2,146 GPT-5 tokens. |
| LangSelect [R](https://arxiv.org/abs/2609.18959) | Generated-code tokens only. | Charges every attempt and fallback. | No prompt or reasoning tokens: weaker than our metric. |
| Self-repair, pass@t [R](https://arxiv.org/abs/2306.09896) | All sampled tokens, feedback included. | A curve over the budget. | Compares repair and new samples at equal cost. |
| SWE-Effi [R](https://arxiv.org/abs/2509.09853) | Tokens, USD, and time. | Failed runs cost more ("expensive failures"). | Area under the curve of resolve rate against budget. |
| Bai et al. [R](https://arxiv.org/abs/2604.22750) | Input and output for each trajectory. | Each run. | Up to 30x variance between runs on one task; input tokens drive the cost. |

### 5.2 How the best work measures errors

| Source | Error classes | Use for us |
|---|---|---|
| ABC-Bench [R](https://arxiv.org/abs/2601.11077) | Syntax, Path Missing, Dependency Missing, Compilation, Logic, Other (Table 4). | The base for environment and build errors. |
| CangjieBench [R](https://arxiv.org/html/2603.14501) | Syntax (foreign), API/library, Type/mutability, Duplicate definition, Runtime exception, Logic error, Timeout. Two LLM annotators; kappa of 0.98 or more. Foreign syntax is 83.9% of the failures of direct generation, and 30.0% with the reference in the prompt. | The base taxonomy. "Syntax (foreign)" is our habit error. |
| PLC [R](https://arxiv.org/abs/2503.13620) | LCPR, CPPR, DMR. | The source language of each habit. |
| Unreliable in Practice? [R](https://arxiv.org/abs/2608.00661) | 15 compile labels and 16 runtime labels for C, C++, Java, Rust. | Fine labels for the compile errors of the baseline arms. |
| MultiPL-E [R](https://arxiv.org/html/2208.08227) | Run-time, Static, Type, Language, Model. Common static errors: "UndefinedIdentifier", "Python-like keywords". | An early habit label. |
| EsoLang-Bench [R](https://arxiv.org/abs/2603.09678); No Resource [R](https://arxiv.org/abs/2606.16827) | Compile, runtime, logic; syntactic against semantic. | A coarse split for summary tables. |
| Aider Polyglot [R](https://raw.githubusercontent.com/Aider-AI/aider/main/aider/website/_data/polyglot_leaderboard.yml) | Malformed responses, syntax errors, indentation errors, lazy comments, context exhaustion, test timeouts. | Counters for harness-level errors. |
| Constraint Decay [R](https://arxiv.org/abs/2605.06445) | Structural verifiers on the diff. | Rule violations, if we add rule levels. |
| BaxBench [R](https://arxiv.org/abs/2502.11844) | Exploits that succeed (sec_pass@1). | A second error metric that costs nothing more. |
| Scaffold Effect [R](https://arxiv.org/abs/2607.22585) | REASON, VERIFY/MAX_TURNS, idle loop, TIME. | Failure modes at the level of the run. |
| Tokenmaxxing [R](https://arxiv.org/abs/2607.22807) | 12 labelled categories of agent actions, for example "Solve in Python, then translate". | Behaviours in the trajectory. |

### 5.3 Proposed metric set [A]

| ID | Metric | Definition | Pattern from |
|---|---|---|---|
| T1 | Output tokens per solved task | Output tokens (reasoning included) of all runs / number of solved runs. | Tokenmaxxing |
| T2 | Total tokens per solved task | (uncached input + cache read + cache write + output) of all runs / number of solved runs. Show each part. | Artificial Analysis, SWE-rebench, Harbor |
| T3 | Cost per solved task | USD with a stated price list and the measured cache-hit rate. | SWE-rebench, Artificial Analysis |
| T4 | Tokens before and after the first pass | T1 split at the first passing snapshot. | Tokenmaxxing |
| T5 | pass@t curve and its area | The solved share against cumulative tokens, up to a fixed budget. | Self-repair, SWE-Effi |
| P1 | Pass within N repair rounds | The share of runs that pass the hidden oracle within N rounds. N is fixed before the run. | Our design; Aider pass_rate_2 |
| P2 | pass@1 ± SE, pass@5, pass all 5 | Over the 5 runs of each task. | SWE-rebench |
| P3 | Pass at the base and the final oracle | Two oracle strengths. | BackendForge |
| E1 | Errors per run, by class | Parse, type or check, habit, test failure, runtime, timeout, environment, harness. | ABC-Bench, CangjieBench, Aider |
| E2 | Habit errors | Per run and per 1,000 output tokens, with the source language of each habit. | CangjieBench, PLC |
| E3 | Repair rounds to green | Checker or test runs before the first pass. | Encore, Zero |
| E4 | Exploits that succeed | From the BaxBench and AutoBaxBench exploits. | BaxBench |
| E5 | Turns and tool calls | From the trajectory. | Harbor ATIF, Zero |
| X1 | Metaprogramming flag | The run writes or runs code in another language to make the solution. Log its tokens. | Metaprogramming study |
| S1 | Static tokens of the reference solution | For each tokenizer and language. | Token Sugar, Hidden Cost, Tokka-Bench |

Rules [A]:

1. Count all runs. A failed run adds its tokens and adds no solve.
2. Report each token type: uncached input, cache read, cache write, reasoning, and output. Input tokens drive the cost of agents [R](https://arxiv.org/abs/2604.22750).
3. State whether a number includes reasoning tokens, and state how cached input is priced. Take the counts from the provider usage, not from a new tokenization.
4. Report each model family apart, because the tokenizers differ.
5. Fix the repair budget before the run. Most gains come in the first 2 to 4 rounds [R](https://arxiv.org/abs/2604.10508) [R](https://arxiv.org/abs/2607.05197). Proposal: log up to 5 rounds, with 3 rounds as the primary cut.
6. A repair round is one checker, compiler, or test run that the agent starts and reads, and the edit after it. Count it from the trajectory.
7. Define a habit error the same way in every arm. In the new language, a rule on our parser errors names the construct (for example "if", "return", "try", or "null"). In a baseline arm, a parse or compile error counts as a habit when a detector assigns its fragment to another language (the PLC method).
8. The compiler of the new language accepts only the canonical form. Formatting is about a quarter of input tokens in the Hidden Cost study [R](https://arxiv.org/abs/2508.13666). Measure the token cost of the canonical form for each tokenizer during the syntax choice, with Tokka-Bench [R](https://github.com/bgub/tokka-bench).

## 6. Fairness and threats to validity

One arm uses a language that no model saw in training. The other arms use languages that every model knows well. The table gives each threat, its evidence, and a control.

| # | Threat | Evidence | Control [A] |
|---|---|---|---|
| 1 | Only one arm gets a reference. | Anka gives a guide only to its own language [R](https://arxiv.org/abs/2512.23214). A 2,146-token reference cuts foreign syntax from 83.9% to 30.0% of the failures in Cangjie [R](https://arxiv.org/html/2603.14501). No-resource languages score 0% to 1% zero-shot [R](https://arxiv.org/abs/2606.16827). | Give each arm a reference of equal length (already in the design). Fill the baseline references with the same topics: a syntax summary, the HTTP framework API, the error model, and the test command. Report the token count of each reference for each tokenizer. |
| 2 | The reference costs input tokens in each turn. | Input tokens drive the cost of agents [R](https://arxiv.org/abs/2604.22750). Tokenmaxxing leaves input tokens out of its main metric because of prefix caching [R](https://arxiv.org/html/2607.22807v2). | Report input tokens with and without the cache. Use the same cache settings in all arms. Count the reference in every arm. |
| 3 | Contamination helps the known languages. | Exercism exercises can be in pre-training data [R](https://arxiv.org/abs/2507.09866). Multi-LCB filters tasks by release date [R](https://arxiv.org/abs/2606.20517). SWE-rebench uses fresh task windows [R](https://swe-rebench.com). | Make the main claim on generated, unpublished tasks (AutoBaxBuilder, the StaminaBench generator, our own family). Report the public sets apart. Keep the main task set private until the results are out. |
| 4 | The agent avoids the new language. | Opus 4.6 solves 64/80 Brainfuck tasks through Python generators; a ban causes "large performance drops" [R](https://arxiv.org/abs/2606.10933). Agents prototype in Python and then translate [R](https://arxiv.org/abs/2607.22807). | Decide a policy before the run. Option A: each arm image holds only its own toolchain and a shell. Option B: allow other languages, count all helper code and its tokens, and set the flag X1. Log the case for each run. |
| 5 | The harness changes the result. | The harness alone changes tokens per solved task up to 40x [R](https://arxiv.org/abs/2607.22585). Harnesses differ up to 6x in passed turns for one model [R](https://arxiv.org/abs/2606.19613). With one scaffold, a ranking is reliable only for that system [R](https://arxiv.org/abs/2610.00651). | One pinned harness version. Two scaffolds. The same turn limit, time limit, and tools in all arms. |
| 6 | A harness bug hits one arm. | In Endoh's benchmark, a Go agent made a symlink that changed later test runs [R](https://danluu.com/pl-tokens/). | A fresh container for each run. A smoke test for each arm with a known reference solution. An audit of sample trajectories in each arm. |
| 7 | Toolchain setup costs differ. | ABC-Bench names environment setup as the main bottleneck [R](https://arxiv.org/abs/2601.11077). Tokenmaxxing preconfigures Cargo and Dune so that agents do not spend turns on setup [R](https://arxiv.org/html/2607.22807v2). | Preconfigure each arm to the same level: the project skeleton, the build file, and the test command. |
| 8 | Visible tests make brittle code. | With visible tests only, agents reach 100% with brittle code [R](https://danluu.com/pl-tokens/). EsoLang-Bench and the metaprogramming study keep the tests hidden [R](https://arxiv.org/abs/2603.09678). | Give the agent visible smoke tests. Grade with hidden tests. Send back only the count of passed hidden tests. |
| 9 | The result depends on the model and the effort level. | The token ratio differs by model [R](https://arxiv.org/abs/2607.22807). The language ranking changes between medium and ultra effort [R](https://danluu.com/pl-tokens/). | Pin the model versions and the reasoning effort. Report each model apart. |
| 10 | Better compiler feedback is part of the gain. | The feedback design matters more than the model [R](https://arxiv.org/abs/2607.05197). | Decide whether the feedback is part of the language (the treatment). State the decision in the report. |
| 11 | A solution in another language harms the result. | A Python reference solution lowers Cangjie scores from 64.0% to 44.5% [R](https://arxiv.org/html/2603.14501). | Put no solution in another language into any prompt. |
| 12 | The model drifts to a familiar language. | Explicit language keywords give the best mitigation [R](https://arxiv.org/abs/2503.13620). | Name the target language in each prompt of each arm. |
| 13 | Tools differ between arms. | The ILA-agent, with doc search and execution tools, scores 16 to 21 points above iterative RAG [R](https://arxiv.org/abs/2602.06976). | Give the same tools in all arms: search over the arm's reference, the compiler, and the test runner. |
| 14 | Popular languages have an advantage. | Popular languages tend to be more correct and cheaper [R](https://danluu.com/pl-tokens/). | This bias works against the new language. Report it as a known bias. |
| 15 | An LLM judge adds noise. | Evaluator agreement is only 31.8% to 93.6% in Vibe Code Bench [R](https://arxiv.org/abs/2603.04601). | Use deterministic oracles only. Use an LLM only to label errors, with a check by a person, as CangjieBench does [R](https://arxiv.org/html/2603.14501). |
| 16 | The agent reads the tests. | The Harbor multi-step verifier leaked tests to the agent; PR #1961 fixed it on 2026-09-14 [R](https://github.com/harbor-framework/harbor/pull/1961). EvoCode-Bench withdrew its earlier numbers [R](https://github.com/UniPat-AI/EvoCodeBench). | Use Harbor v0.24.0 or later. Make sure that the agent cannot read the hidden tests. |
| 17 | The HTTP layer differs. | The oracles speak HTTP [R](https://github.com/logic-star-ai/baxbench). The new language describes state machines that read envelopes. | The runtime of the new language gives a fixed HTTP gateway. Each baseline arm gets one fixed framework. Both come pre-installed, and the agent does not write them. |

## 7. Harness and statistics recommendation

### 7.1 Harness [A]

1. Use Harbor as the one runner for all arms. Pin one version, v0.24.0 or later (v0.26.0 on 2026-11-13) [R](https://github.com/harbor-framework/harbor/releases).
2. Package each task once for each arm as a Harbor task: a Dockerfile with the toolchain of the arm, instruction.md, and tests/test.sh. CangjieBench-harbor is a ready example for a new language [R](https://github.com/cjhCoder7/CangjieBench).
3. Let test.sh write reward.json with these fields: tests_passed, tests_total, compile_ok, check_errors, habit_errors, exploits_passed. Harbor accepts multi-dimensional rewards [R](https://docs.harborframework.com/tasks/overview.md).
4. Run 5 attempts for each task with -k 5 [R](https://docs.harborframework.com/jobs/run-a-job.md).
5. Use mini-swe-agent as the main scaffold, because it is minimal and the Tokenmaxxing study used it [R](https://arxiv.org/abs/2607.22807). Use one native CLI agent as the second scaffold. Pin both versions.
6. Use the same turn limit and time limit in all arms. Tokenmaxxing used 40 turns and 10 minutes for small tasks [R](https://arxiv.org/abs/2607.22807). BackendForge allows 500 model calls for backend tasks [R](https://github.com/PKU-ASE-RISE/BackendForge). Set our limits after the pilot.
7. Take tokens and USD from the Harbor AgentContext. Take turns, tool calls, and checker calls from the ATIF trajectory [R](https://docs.harborframework.com/agents/atif). Take reasoning tokens from the provider usage, because Harbor has no separate field [R](https://github.com/harbor-framework/harbor).
8. Use the regrade command to apply a new or fixed oracle to old runs. It does not run the agent again [R](https://docs.harborframework.com/tasks/overview.md).
9. Alternative: Inspect AI, if we want the statistics inside the harness (epochs, pass_at_k, clustered stderr) [R](https://inspect.aisi.org.uk/metrics.html). Do not mix two harnesses in one comparison.

### 7.2 Statistics [A]

1. The unit of analysis is the task. Keep all arms of a task together in each resample.
2. Token claim, primary: the ratio of tokens per solved task (the new language against each baseline). Use a paired bootstrap over tasks, clustered by task family.
3. Token claim, second analysis: an LMM of log(output tokens) with language as a fixed effect and a random intercept for each task, fitted with REML for each model. Report exp(coefficient) with a 95% CI, as Tokenmaxxing does [R](https://arxiv.org/abs/2607.22807). The high ICC (0.73 to 0.97) in that study supports a paired design.
4. Pass and error claims: per-task paired differences with a clustered SE [R](https://arxiv.org/abs/2411.00640). For single paired runs, use McNemar with Benjamini-Hochberg [R](https://arxiv.org/abs/2606.16827). For error counts per run, use a mixed Poisson or negative binomial model with a task random effect.
5. Six arms: an LMM with language as a fixed effect and task as a random effect. Correct for multiple comparisons: Tukey for balanced data [R](https://arxiv.org/abs/2608.22659), Holm or Benjamini-Hochberg in other cases.
6. Power: run a pilot of about 30 tasks. Estimate the variances. Compute N* and q with Kotawala's method [R](https://arxiv.org/abs/2605.30315) or Miller's Eq. 9 [R](https://arxiv.org/abs/2411.00640). Use Wang's split of noise to choose between more runs and more tasks [R](https://arxiv.org/abs/2512.21326).
7. Small subsets (one task family, one error class): use Bayesian intervals with bayes_evals or scorio [R](https://arxiv.org/abs/2503.01747) [R](https://arxiv.org/abs/2510.04265).
8. Report each model family and each scaffold apart. Make a claim about the language only when it holds in both scaffolds and both families [R](https://arxiv.org/abs/2610.00651).
9. Pre-register the hypotheses, metrics, budgets, exclusion rules, and the metaprogramming policy before the main run. Dan Luu pre-registered his guesses [R](https://danluu.com/pl-tokens/).

### 7.3 Report layout [A]

Copy the columns of SWE-rebench, Artificial Analysis, and Vibe Code Bench [R](https://swe-rebench.com) [R](https://artificialanalysis.ai/methodology/coding-agents-benchmarking) [R](https://www.vals.ai/benchmarks/vibe-code). One row for each arm, model, and scaffold: pass@1 ± SE, pass@5, pass all 5, tokens per solved task by type, cost per solved task, turns, repair rounds, errors per run by class, habit errors, and duration.

## 8. Gaps and open questions

### 8.1 Gaps (the sweep found no source) [A]

1. No backend benchmark keeps the tasks fixed across languages and also reports tokens per solved task.
2. No benchmark covers durable workflows: logs, timers, retries with backoff, or exactly-once outputs.
3. No tool classifies habit errors in a new language. The PLC detectors and the CangjieBench LLM annotators do not know our constructs. We need a rule-based classifier on our parser errors.
4. No study gives a reference of equal length to each arm. A reviewer will ask how we filled the baseline references.
5. No published result compares a language for agents with established languages on agent tokens. Zero publishes no comparison [R](https://github.com/vercel-labs/zerolang). Anka reports no tokens [R](https://arxiv.org/abs/2512.23214).
6. Some artifacts are not released: the Tokenmaxxing code and data [R](https://arxiv.org/abs/2607.22807), the LangSelect artifact (HTTP 410) [R](https://arxiv.org/abs/2609.18959), the ILA-agent benchmark [R](https://arxiv.org/abs/2602.06976), and the metaprogramming harness (anonymous supplement only) [R](https://arxiv.org/abs/2606.10933).

### 8.2 Open questions for Piotr

| # | Question | Why it matters |
|---|---|---|
| 1 | Is the eval research only, or part of a commercial deliverable? | Non-commercial licences: StaminaBench, EvoCode-Bench data, Multi-LCB data, the PLC and SWE-Effi papers. No licence file: Constraint Decay, Encore, ABC-Bench code, Agnostics, PLC code, Endoh, Tokka-Bench, Token Sugar, SimPy, self-repair. |
| 2 | Which policy for metaprogramming: ban other toolchains in the arm image, or count the helper code? | It changes the token and error counts of the new-language arm (threat 4). |
| 3 | What goes into the reference of equal length for each baseline arm? | No prior study did this (gap 4). |
| 4 | Is the quality of compiler feedback part of the treatment? | It decides what the claim means (threat 10). |
| 5 | Who provides the HTTP layer, and which framework does each baseline arm get? | BaxBench offers 14 frameworks [R](https://github.com/logic-star-ai/baxbench). The choice changes the baseline results (threat 17). |
| 6 | Which two model families, which two scaffolds, which effort level, and which budget? | Estimate [A]: 200 to 550 tasks × 5 runs × 6 arms × 2 families = 12,000 to 33,000 runs for each scaffold. At USD 0.44 per run (Encore, small tasks [R](https://github.com/encoredev/ai-backend-benchmark)) to USD 5.55 per run (BackendForge, large tasks [R](https://arxiv.org/abs/2607.11042)), the cost is about USD 5,000 to 183,000 for each scaffold. |
| 7 | Which oracle interface controls the clock and the faults in the durable-machine family? | Every arm must implement it (section 4). |
| 8 | Do we write to authors? | Tokenmaxxing (code and data); Constraint Decay, Encore, Agnostics, and Endoh (licences). |
| 9 | Do we keep the main task set private? | Contamination of later models (threat 3). |

### 8.3 Leads that no verify pass checked

The sweep agents reported these items, but the verify pass did not check them. Check each one before use.

| Lead | Why check it |
|---|---|
| "Identical Runs, Different Results" [arXiv 2609.33812](https://arxiv.org/abs/2609.33812) | Number of runs needed to separate agents; cache effects on cost. |
| evalstats [arXiv 2609.35815](https://arxiv.org/abs/2609.35815) | Warns against bootstrap CIs for N < 100. |
| "How Many Tasks Are Enough" [arXiv 2607.12338](https://arxiv.org/abs/2607.12338) | Task count. |
| HAL [arXiv 2510.11977](https://arxiv.org/abs/2510.11977) | A cost-aware agent harness. |
| Testing LLM-Generated Distributed Protocol Code (PLDI 2026 PAgE) [page](https://pldi26.sigplan.org/details/page-2026-papers/5/Testing-LLM-Generated-Distributed-Protocol-Code) | Lost, delayed, and duplicated messages: near to durable machines. No paper found. |
| SysMoBench [arXiv 2509.23130](https://arxiv.org/abs/2509.23130); CONCUR [arXiv 2603.03683](https://arxiv.org/abs/2603.03683) | State-machine models and concurrency checks. |
| Chess engines in 17 languages [arXiv 2606.13763](https://arxiv.org/abs/2606.13763) | Cost rises for less common languages. |
| E2EDev [arXiv 2510.14509](https://arxiv.org/abs/2510.14509); SWE-PolyBench [arXiv 2504.08703](https://arxiv.org/abs/2504.08703); SWE-Bench Pro [arXiv 2509.16941](https://arxiv.org/abs/2509.16941) | Other task sets. |
| Cost-inefficient behaviours of coding agents [arXiv 2609.30725](https://arxiv.org/abs/2609.30725); "Beyond Human-Readable" [arXiv 2604.07502](https://arxiv.org/abs/2604.07502) | Waste in agent runs; shorter input can raise total cost. |
| Kiro diagnostics by language [blog](https://kiro.dev/blog/diagnostics-over-time/) | Static-analyzer error rate for each language. |
| Martin Alderson, static token count on Rosetta Code [post](https://martinalderson.com/posts/which-programming-languages-are-most-token-efficient/) | Dan Luu criticizes it: the tasks are trivial. |

## 9. Sources

All links were checked by the sweep and verify agents on 2026-11-20.

Backend benchmarks:
- BackendForge: https://arxiv.org/abs/2607.11042, https://arxiv.org/html/2607.11042, https://aclanthology.org/2026.findings-emnlp.2236/, https://github.com/PKU-ASE-RISE/BackendForge, https://github.com/PKU-ASE-RISE/BackendForge/blob/main/docs/EVALUATION.md
- StaminaBench: https://arxiv.org/abs/2606.19613, https://arxiv.org/html/2606.19613, https://github.com/amazon-science/StaminaBench
- AutoBaxBench / AutoBaxBuilder: https://arxiv.org/abs/2512.21132, https://github.com/eth-sri/AutoBaxBuilder, https://huggingface.co/datasets/eth-sri/AutoBaxBench
- BaxBench: https://arxiv.org/abs/2502.11844, https://github.com/logic-star-ai/baxbench, https://github.com/logic-star-ai/baxbench/releases, https://baxbench.com, https://huggingface.co/datasets/LogicStar/BaxBench
- ABC-Bench: https://arxiv.org/abs/2601.11077, https://aclanthology.org/2026.findings-acl.1142/, https://huggingface.co/datasets/OpenMOSS-Team/ABC-Bench, https://github.com/OpenMOSS/ABC-Bench
- Constraint Decay: https://arxiv.org/abs/2605.06445, https://github.com/francdente/constraint-decay, https://colm.cc/Conferences/2026/AcceptedPapers
- RealWorld: https://github.com/realworld-apps/realworld
- RepoGenesis: https://arxiv.org/abs/2601.13943, https://github.com/microsoft/DKI_LLM/tree/main/RepoGenesis
- Encore: https://github.com/encoredev/ai-backend-benchmark, https://encore.dev/blog/ai-benchmark
- EvoCode-Bench: https://arxiv.org/abs/2605.24110, https://github.com/UniPat-AI/EvoCodeBench, https://huggingface.co/datasets/UnipatAI/EvoCodeBench
- Vibe Code Bench: https://www.vals.ai/benchmarks/vibe-code, https://arxiv.org/abs/2603.04601

Multi-language and new-language task sets:
- Multi-LCB: https://arxiv.org/abs/2606.20517, https://github.com/Multi-LCB/Multi-LCB, https://openreview.net/forum?id=MKxKKsz0cx
- Agnostics: https://arxiv.org/abs/2508.04865, https://github.com/nuprl/agnostics-framework, http://abgru.me/project/agnostics
- EsoLang-Bench: https://arxiv.org/abs/2603.09678, https://github.com/Lossfunk/EsolangBench, https://huggingface.co/datasets/Lossfunk/Esolang-Bench
- CangjieBench: https://arxiv.org/abs/2603.14501, https://arxiv.org/html/2603.14501, https://github.com/cjhCoder7/CangjieBench
- No Resource, No Benchmarks, No Problem?: https://arxiv.org/abs/2606.16827, https://doi.org/10.5281/zenodo.19366887
- AlgoVeri: https://arxiv.org/abs/2602.09464, https://github.com/haoyuzhao123/algoveri; vericoding: https://arxiv.org/abs/2509.22908
- AutoCodeBench: https://arxiv.org/abs/2508.09101, https://github.com/Tencent-Hunyuan/AutoCodeBenchmark
- MultiPL-E: https://github.com/nuprl/MultiPL-E, https://raw.githubusercontent.com/nuprl/MultiPL-E/main/LICENSE, https://huggingface.co/datasets/nuprl/MultiPL-E, https://arxiv.org/html/2208.08227
- Aider Polyglot: https://aider.chat/2024/12/21/polyglot.html, https://raw.githubusercontent.com/Aider-AI/aider/main/aider/website/_data/polyglot_leaderboard.yml, https://github.com/Aider-AI/polyglot-benchmark; LiveRepoReflection: https://arxiv.org/abs/2507.09866
- Zero: https://github.com/vercel-labs/zerolang, https://github.com/vercel-labs/zerolang/blob/main/evals/README.md, https://github.com/vercel-labs/zerolang/blob/main/evals/src/run.ts, https://github.com/vercel-labs/zerolang/blob/main/benchmarks/rosetta/README.md

Harnesses and agents:
- Harbor: https://github.com/harbor-framework/harbor, https://github.com/harbor-framework/harbor/releases, https://pypi.org/project/harbor/, https://raw.githubusercontent.com/harbor-framework/harbor/main/src/harbor/models/agent/context.py, https://docs.harborframework.com/tasks/overview.md, https://docs.harborframework.com/jobs/run-a-job.md, https://docs.harborframework.com/agents/atif, https://github.com/harbor-framework/harbor/pull/1961, https://www.tbench.ai/leaderboard, https://arxiv.org/abs/2601.11868, https://arxiv.org/abs/2609.04298
- Inspect AI: https://pypi.org/project/inspect-ai/, https://inspect.aisi.org.uk/sandboxing.html, https://inspect.aisi.org.uk/dataframe.html, https://inspect.aisi.org.uk/metrics.html, https://inspect.aisi.org.uk/setting-limits.html
- mini-swe-agent: https://github.com/SWE-agent/mini-swe-agent, https://raw.githubusercontent.com/SWE-agent/mini-swe-agent/main/docs/usage/output_files.md, https://raw.githubusercontent.com/SWE-bench/swe-bench.github.io/master/js/mainResults.js
- SWE-bench family: https://github.com/SWE-bench/SWE-bench, https://www.swebench.com/multilingual.html, https://huggingface.co/datasets/SWE-bench/SWE-bench_Multilingual, https://arxiv.org/abs/2504.02605, https://github.com/multi-swe-bench/multi-swe-bench; ProgramBench: https://arxiv.org/abs/2605.03546, https://programbench.com/

Studies and methods:
- Tokenmaxxing: https://arxiv.org/abs/2607.22807, https://arxiv.org/html/2607.22807v2, https://conf.researchr.org/home/splash-issta-2026/lmpl-2026
- Metaprogramming: https://arxiv.org/abs/2606.10933, https://neurips.cc/virtual/2026/poster/152963
- PLC: https://arxiv.org/abs/2503.13620, https://github.com/TruX-DTF/PLC
- Unreliable in Practice?: https://arxiv.org/abs/2608.00661
- ILA-agent: https://arxiv.org/abs/2602.06976
- Anka: https://arxiv.org/abs/2512.23214, https://github.com/BleBlo/Anka
- Bai et al.: https://arxiv.org/abs/2604.22750, https://resource-aware-workshop.github.io/; related: https://arxiv.org/abs/2611.07238
- Self-repair: https://arxiv.org/abs/2306.09896, https://github.com/theoxo/self-repair, https://arxiv.org/abs/2604.10508, https://arxiv.org/abs/2607.05197
- SWE-Effi: https://arxiv.org/abs/2509.09853, https://github.com/Centre-for-Software-Excellence/SWE-Effi
- Dan Luu: https://danluu.com/pl-tokens/
- Endoh: https://github.com/mame/ai-coding-lang-bench, https://raw.githubusercontent.com/mame/ai-coding-lang-bench/main/benchmark.rb
- LangSelect: https://arxiv.org/abs/2609.18959
- Tokka-Bench: https://arxiv.org/abs/2610.08794, https://github.com/bgub/tokka-bench
- Token Sugar, Hidden Cost, SimPy: https://arxiv.org/abs/2512.08266, https://arxiv.org/abs/2508.13666, https://arxiv.org/abs/2404.16333, https://github.com/v587su/TokenSugar, https://github.com/v587su/SimPy

Leaderboards:
- SWE-rebench: https://swe-rebench.com, https://teletype.in/@ibragim_bad/swe-rebench-2026-07, https://arxiv.org/abs/2602.23866, https://huggingface.co/datasets/nebius/SWE-rebench-V2
- Artificial Analysis: https://artificialanalysis.ai/methodology/coding-agents-benchmarking
- Terminal-Bench: https://www.tbench.ai/leaderboard, https://www.tbench.ai/run

Statistics:
- Miller: https://arxiv.org/abs/2411.00640
- Wang: https://arxiv.org/abs/2512.21326, https://all-the-noises.github.io
- Mandujano Reyes: https://arxiv.org/abs/2608.22659
- Kotawala: https://arxiv.org/abs/2605.30315
- Hardy et al.: https://arxiv.org/abs/2610.00651
- Vats and Golev: https://arxiv.org/abs/2607.22585
- Bowyer et al., Hariri et al.: https://arxiv.org/abs/2503.01747, https://arxiv.org/abs/2510.04265, https://github.com/sambowyer/bayes_evals, https://github.com/mohsenhariri/scorio

Refuted: no candidate got the verdict "refuted". The verify pass refuted these sweep claims, and the note uses the corrected facts: BackendForge "artifacts not released" and "two oracle levels"; Tokenmaxxing "Table 17 gives turns", "input tokens not counted", and "Python cheapest for all models"; EvoCode-Bench "NeurIPS 2026" and its paper numbers; Encore "token counts in the blog" and "pure HTTP oracle"; BaxBench "about 35% correct and secure" (about 38%); metaprogramming study "solved out of 80" (mean percent); CangjieBench "four settings" and "no licence"; AutoCodeBench and SWE-bench Multilingual "no licence"; MultiPL-E "repo is MIT"; mini-swe-agent "separate Bash Only board"; LangSelect "languages not named"; Endoh "Rust failures"; Token Sugar "replaces SimPy" and "no repos"; SWE-Effi "three scores" and "no repo"; ILA-agent "type lookup matters most"; PLC "FPR needs all tests" and "CPPR in the target language"; No Resource "no replication package"; Miller "n = 969 with K = 1"; Mandujano Reyes "no named correction method".
