# Scala.js Migration Plan for Princess

Date: 2026-02-22

## Goal and scope

This document lists **blocking issues** to run Princess on Scala.js, evaluates moving parsing to a pure-Scala parser (cats-parse), and proposes a phased work schedule.

Assumptions used for this plan:

- Primary target is a Scala.js library build (browser and/or Node), not a JVM CLI binary.
- Required minimum feature set for first usable Scala.js release:
  - parse SMT-LIB from strings/readers,
  - run core solving APIs,
  - expose results without JVM threads/queues.
- JVM-only entry points (CLI, Swing UI, daemon server, portfolio multi-threading) can remain JVM modules.

## Executive summary

The largest blockers are:

1. Parser stack depends on generated Java/CUP/JFlex parsers and JVM jars.
2. Core API execution model depends on JVM threads and blocking queues.
3. Build is not set up as a Scala.js cross-project and uses JVM-only dependency wiring.
4. Core code has coupling to `CmdlMain` (CLI object), which drags JVM-only code into library paths.

A realistic path is:

- split into `core` (cross JVM/JS) and `jvm-app` modules,
- replace SMT-LIB and Princess parsers with cats-parse (or equivalent pure Scala parser),
- replace `Thread`/`LinkedBlockingQueue`/`ConcurrentHashMap` usage in shared code with Scala.js-safe primitives,
- keep CLI/server/GUI/portfolio parallel execution in JVM-only module.

## Blocking issues

### B1. Build architecture is JVM-only

**Evidence**

- `build.sbt:73-90` wires `parser` and `smt-parser` subprojects around prebuilt JVM jars.
- `build.sbt:95-99` makes root depend on those parser subprojects.
- `build.sbt:112-116` adds JVM `java-cup-runtime` and JVM dependency style (`%%`) for parser-combinators.
- `project/assembly.sbt:1-2` has assembly/native-image setup, but no Scala.js plugin/cross-project setup.

**Why this blocks Scala.js**

Scala.js cannot consume JVM bytecode parser jars (`parser.jar`, `smt-parser.jar`) as source-level JS-compatible code.

**Required action**

- Introduce cross-project layout (`coreJVM/coreJS`).
- Remove parser-jar dependency from shared module.
- Add Scala.js plugin and JS-specific dependency coordinates (`%%%` where needed).

---

### B2. SMT-LIB parser is generated Java (BNFC + CUP + JFlex)

**Evidence**

- `smt-parser/Makefile:18-36` generates Java lexer/parser with BNFC/CUP/JFlex.
- `src/main/scala/ap/parser/SMTParser2InputAbsy.scala:57-58` imports generated `ap.parser.smtlib` AST/parser classes.
- `src/main/scala/ap/parser/SMTParser2InputAbsy.scala:229-230` instantiates generated `Yylex` and `parser`.
- `src/main/scala/ap/parser/SMTParsingUtils.scala:37-38` imports generated classes; `:47-48` uses generated parser.
- `src/main/scala/ap/parser/SMTParseableTheory.scala:37` and `:95-106` expose generated AST types in extension interfaces.

**Why this blocks Scala.js**

Generated parser/AST classes are Java bytecode and JVM runtime dependent.

**Required action**

- Replace with pure Scala parser implementation (cats-parse recommended).
- Define Scala AST model and remove/bridge `smtlib.Absyn.*` from shared interfaces.

---

### B3. Princess `.pri` parser is generated Java (BNFC + CUP + JFlex)

**Evidence**

- `parser/Makefile:34-50` generates Java lexer/parser and classes.
- `src/main/scala/ap/parser/ApParser2InputAbsy.scala:46-47` imports generated `ap.parser.ap_input.*` classes.
- `src/main/scala/ap/parser/ApParser2InputAbsy.scala:87-88` uses generated `Yylex` and `parser`.

**Why this blocks Scala.js**

Same root issue as SMT-LIB parser: JVM generated parser stack.

**Required action**

- Port `.pri` grammar to pure Scala parser (cats-parse).
- Keep translator logic but retarget it to pure Scala AST.

---

### B4. Core solving API uses JVM threading + blocking queues

**Evidence**

- `src/main/scala/ap/api/SimpleAPI.scala:58` imports `LinkedBlockingQueue` and `TimeUnit`.
- `src/main/scala/ap/api/SimpleAPI.scala:4462-4475` creates blocking queues and a dedicated `Thread`.
- `src/main/scala/ap/api/SimpleAPI.scala:2144-2147` calls blocking/polling queue methods.
- `src/main/scala/ap/api/ProofThread.scala:44` imports `LinkedBlockingQueue`; `:104` uses `.take`.

**Why this blocks Scala.js**

Scala.js has no JVM threads or blocking queue semantics.

**Required action**

- Replace proof-thread command loop with Scala.js-safe async model (Future/Promise/event loop), or a synchronous single-thread mode with explicit async wrapper.

---

### B5. Additional JVM concurrency primitives in shared/near-shared code

**Evidence**

- `src/main/scala/ap/util/OpCounters.scala:40-41` uses `ConcurrentHashMap` and `LongAdder`.
- `src/main/scala/ap/util/Timer.scala:39` imports `java.lang.Thread` and checks thread identity at `:87-88`.
- `src/main/scala/ap/ParallelFileProver.scala:44,47,492` uses `SyncVar`, blocking queues, and threads.
- `src/main/scala/ap/ServerMain.scala:39,95` uses `Semaphore` and threads.
- `src/main/scala/ap/interpolants/WolverineInterface.scala:39,111,148` uses `Executors` and `Await.result`.

**Why this blocks Scala.js**

These APIs are JVM-only or rely on blocking semantics not available in Scala.js.

**Required action**

- In shared code: replace with Scala collections + `Future`/`Promise` primitives.
- Move server/portfolio/daemon behavior to JVM-only modules.

---

### B6. Core code is coupled to CLI object (`CmdlMain`)

**Evidence**

- `src/main/scala/ap/api/SimpleAPI.scala:66` references `CmdlMain.version`.
- `src/main/scala/ap/api/SimpleAPI.scala:2425` calls `CmdlMain.doPrintTextCertificate`.
- `src/main/scala/ap/parser/SMTParser2InputAbsy.scala:1591,1597` uses `CmdlMain.printGreeting/version`.
- `src/main/scala/ap/proof/ConstraintSimplifier.scala:158,161` uses `CmdlMain.NullStream`.
- `src/main/scala/ap/theories/nia/Gaussian.scala:73` uses `CmdlMain.NullStream`.

**Why this blocks Scala.js**

`CmdlMain` is CLI-centric and includes JVM file/process style logic. This coupling prevents clean `core` extraction.

**Required action**

- Extract shared constants/utilities (`version`, null output stream, certificate formatting facade) into platform-neutral modules.
- Keep CLI wiring in JVM module.

---

### B7. File/network/UI features are JVM-specific and must be isolated

**Evidence**

- `src/main/scala/ap/CmdlMain.scala:267,288,379,1039` uses `FileOutputStream`/`FileReader`.
- `src/main/scala/ap/JavaWrapper.scala:82-86` uses `java.io.File`/`FileReader`.
- `src/main/scala/ap/parser/TPTPTParser.scala:1384-1387` resolves includes via env var + `FileReader`.
- `src/main/scala/ap/ServerMain.scala:41,64` uses `java.net.ServerSocket`.
- `src/main/scala/ap/DialogMain.scala:44-46` uses Swing/AWT.

**Why this blocks Scala.js**

No JVM filesystem/socket/Swing in Scala.js runtime.

**Required action**

- Put these features in JVM-only modules.
- For JS, expose string/reader-based APIs and optional host callbacks for include/file resolution.

---

### B8. Scala version baseline needs simplification for Scala.js work

**Evidence**

- `build.sbt:56-57` cross-builds `2.11.12` and `2.12.20`.

**Why this blocks or slows migration**

Practical Scala.js migration + modern parser libraries is significantly easier if shared code targets one modern Scala line (at least 2.12, usually 2.13+).

**Required action**

- Drop 2.11 in shared module migration branch.
- Stabilize on one Scala line for cross-platform core during migration.

## Parser migration evaluation (cats-parse)

## Current parser landscape

- SMT-LIB: Java-generated parser + Java-generated AST + large Scala translator (`SMTParser2InputAbsy.scala`, ~4.4k LOC).
- Princess `.pri`: Java-generated parser + AST + large translator (`ApParser2InputAbsy.scala`, ~1.3k LOC).
- TPTP: already pure Scala parser combinators (`TPTPTParser.scala`), but with JVM file-include behavior.

## Why cats-parse is a good fit

- Pure Scala, Scala.js compatible.
- Fine-grained control over lexical and syntactic layers.
- Deterministic behavior and explicit error reporting.
- Avoids generated Java artifacts and Java collection bridging.

## Major migration design choices

### Choice 1: AST compatibility vs direct translation

- **AST compatibility approach (recommended first)**:
  - create pure Scala ASTs matching current translator expectations,
  - keep most semantic translation logic in place,
  - reduces churn and regression risk.
- **Direct translation approach**:
  - parse directly into `IExpression`/internal forms,
  - less intermediate AST code long-term,
  - much higher short-term risk and rewrite cost.

### Choice 2: TPTP parser now vs later

- Keep existing TPTP parser-combinators initially and only isolate file include (`include(...)`) behind callback.
- Optional later migration of TPTP to cats-parse for uniformity/performance.

## Estimated effort for parser migration

- SMT-LIB parser + incremental command stream parity: **3-4 weeks**.
- `.pri` parser parity: **2-3 weeks**.
- TPTP parser port to cats-parse (optional): **1-2 weeks**.

## Concurrency migration evaluation (Scala.js-safe primitives)

## Current model

- `SimpleAPI` offloads solving to a dedicated JVM thread and communicates through blocking queues.
- External API offers polling/blocking status retrieval.

## Scala.js-safe replacement options

### Option A: Synchronous core + async facade (recommended)

- Core solver runs synchronously in same thread.
- JS facade exposes `Future`-based API for host integration.
- In browser, run solver in a Web Worker for responsiveness.

Pros:

- Minimal invasive changes to solver internals.
- Clear separation between solver determinism and host scheduling.

Cons:

- Some `SimpleAPI` status semantics (`Running`, blocking `getStatus(true)`) need adaptation/deprecation in JS profile.

### Option B: Fully async command loop in shared code

- Reimplement command processing as Promise/Future mailbox.

Pros:

- Closer to current command architecture.

Cons:

- More complexity without true parallelism in Scala.js.

## Concrete replacements

- `Thread` + `LinkedBlockingQueue` -> `Future`/`Promise` + immutable/mutable queue in event loop.
- `poll(timeout, TimeUnit)` -> deadline-aware Future composition (no blocking).
- `ConcurrentHashMap`/`LongAdder` -> plain mutable map counters in JS/shared path.
- `Await.result` -> non-blocking Future chains.

## Proposed target architecture

- `princess-core` (cross JVM/JS):
  - solver core,
  - parser frontends (pure Scala),
  - shared utilities,
  - cross-platform API surface.
- `princess-jvm-app` (JVM only):
  - `CmdlMain`, `ServerMain`, `DialogMain`, `ParallelFileProver`, `JavaWrapper`, warmup/daemon features.
- `princess-js` (JS only wrappers):
  - JS-friendly entrypoints,
  - worker integration helpers,
  - optional include/file resolver callbacks.

## Detailed work plan and schedule

Schedule below assumes **2 engineers full-time** and aims for a first JS release in ~10 weeks.

### Phase 0 (Week 1): migration scaffolding and decisions

Deliverables:

- Define target runtime matrix (browser, Node, or both).
- Create module split (`core` cross-project + JVM app module).
- Add Scala.js build plumbing and first empty JS compile target.

Exit criteria:

- `coreJS` compiles with a minimal placeholder API.
- JVM app still builds unchanged.

### Phase 1 (Weeks 2-3): decouple core from JVM app objects

Tasks:

- Remove direct references from core to `CmdlMain` (`SimpleAPI`, parser get-info path, simplifier, gaussian).
- Introduce shared constants/util abstractions.
- Move clearly JVM-only files to JVM module (CLI/server/gui/portfolio wrappers).

Exit criteria:

- Shared module has no references to JVM entrypoint classes.
- No `java.net`, Swing/AWT, or daemon/server code in shared sources.

### Phase 2 (Weeks 3-6): parser migration to pure Scala

Tasks:

- Implement SMT-LIB lexer/parser in cats-parse.
- Preserve incremental SMT command processing behavior currently in `processIncrementally`.
- Implement `.pri` parser in cats-parse.
- Bridge/replace `SMTParseableTheory` AST interfaces.

Test plan:

- Reuse `testcases/smtlib-parser` and `testcases/adt` parser-heavy suites.
- Add parser roundtrip/error-location checks.

Exit criteria:

- No dependency on `parser.jar`, `smt-parser.jar`, `java-cup-runtime` in shared module.
- Parser regression suites pass at agreed threshold (>= 99% identical outputs, known deltas documented).

### Phase 3 (Weeks 6-8): concurrency and API execution model

Tasks:

- Replace `SimpleAPI` proof-thread queue model with JS-safe model (recommended Option A).
- Remove blocking queue operations in shared API.
- Refactor `OpCounters` and `Timer` implementations for cross-platform compatibility.

Test plan:

- API behavioral tests for `checkSat` / status transitions / model extraction.
- Timeout and cancellation contract tests in JVM and JS profiles.

Exit criteria:

- Shared module has no `java.util.concurrent.*` usage.
- JS build exposes non-blocking API with documented semantics.

### Phase 4 (Weeks 8-9): platform adapters and feature gating

Tasks:

- JVM module keeps CLI/server/portfolio behavior.
- JS module adds browser/Node adapters (input from strings; optional include resolver for TPTP).
- Explicitly gate unsupported features in JS (server daemon, Swing UI, multi-thread portfolio).

Exit criteria:

- Feature matrix document completed.
- JS runtime behavior for unsupported features is explicit (compile-time exclusion or clear runtime error).

### Phase 5 (Weeks 9-10): stabilization and release prep

Tasks:

- Performance baseline against representative SMT-LIB workloads.
- Memory and responsiveness checks for browser worker integration.
- Documentation and migration notes for API users.

Exit criteria:

- Green CI for JVM + JS core builds.
- Release candidate with known-issues list.

## Risk register and mitigations

1. Parser parity regressions (highest risk).
   - Mitigation: preserve translator behavior; run full parser corpus on each milestone.
2. API semantic drift from blocking to async model.
   - Mitigation: define JS-specific status contract early and keep compatibility wrappers on JVM.
3. Hidden core/JVM coupling.
   - Mitigation: enforce module boundaries in build; fail CI on forbidden package imports.
4. Browser responsiveness for heavy proofs.
   - Mitigation: worker-based execution from first JS beta.

## Acceptance criteria for “Scala.js-ready”

- Shared core compiles/runs on Scala.js without JVM parser jars and without Java concurrency APIs.
- SMT-LIB parsing and solving works from string input in JS runtime.
- Core test subset passes in both JVM and JS pipelines.
- JVM-specific tools remain available through dedicated JVM module.

## Immediate next actions (first 2 weeks)

1. Create `core` cross-project and move solver/parser/shared files there.
2. Remove direct `CmdlMain` dependencies from shared code.
3. Prototype cats-parse SMT-LIB command parser for `(set-logic ...)`, `(assert ...)`, `(check-sat)`, `(exit)` plus error reporting.
4. Decide and document JS API contract (`Future`-first vs status polling emulation).

