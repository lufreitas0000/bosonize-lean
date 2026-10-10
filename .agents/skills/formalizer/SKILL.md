---
name: formalizer
description: Draft, prove, and audit Bosonize-Lean chapters with mirrored notebooks and frozen interfaces. Use for chapter formalization and review of proposed Lean definitions or proofs in this repository.
---

# Bosonize-Lean formalizer

Translate the project's 1+1D lattice field-theory notes into rigorous Lean 4. Follow the chapter dependency graph and [Lean conventions](../../rules/lean_conventions.md). Use the installed compiler as the authority for elaboration and proof checking; notes, appendices, and suggested code still need mathematical scrutiny.

For authorized chapter development, follow the repository's automatic A–B–C policy: independently review Phase A, establish the reviewed lock, prove in Phase B, then audit/promote/freeze in Phase C without routine human confirmation. Read [Pipeline and independent review](references/pipeline.md) for transition criteria, reviewer duties, interface corrections and escalation. Honor an explicit instruction to stop at a particular phase or only review/update the workflow. Do not select further chapters beyond the authorized scope. Preserve unrelated worktree edits and upstream locked Core sources.

## Usage allowance and checkpoints

Check live Codex usage before chapters, phase transitions and parallel proof groups, and approximately every 5–10 minutes during sustained work. If less than 10% of the five-hour allowance or less than 5% of the weekly allowance remains, warn, stop new proof work, save a resumable checkpoint and yield with a recommendation to pause. Follow [Usage allowance and resumable checkpoints](references/usage_budget.md) for tool availability, shared-account limits, delegated work and resumption. This guard can defer an otherwise automatic A–B–C transition; it never relaxes proof or freeze requirements.

## Source reconciliation and proof design

Read the chapter, `notes/md/TOC.md`, and chapter-relevant appendices in `notes/appendices/`. Consult `docs/stub_suggestion/` for interfaces and `docs/proof_suggestion/` for proofs. Follow cross-references to applicable review corrections; dated reviews describe snapshots, so check whether each finding still applies to the current source.

Compare statements and sketches with their actual carriers, adjoints, character assumptions, and downstream uses. A sketch guides proof search only after these contracts are checked. Record adopted, adapted, and rejected ideas in the companion notebook. If a source claim is false or underspecified, report the counterexample or missing obligation and propose a correction; do not silently weaken the theorem or change an operator to make it provable.

Read the relevant sections of [Proof design](references/proof_design.md) when drafting or proving statements involving restricted operators, noncommutative products, current margins, exponentials, states, or model equivalences. Its topic table routes to the needed sections; loading every chapter or every example is unnecessary for a local goal.

Essential checks:

- Identify the carrier and source/target of each map; retain projection remainders unless proved zero.
- Preserve product order, commutator signs, and adjoint reversal. Separate scalar algebra from operator identities.
- Attach margins to the inputs where the restricted identity is applied. Prefer useful local hypotheses, with stronger convenient wrappers only when justified.
- Establish existence/nonzero-action evidence where the claim requires it. A nonempty subspace does not establish a positive vacuum state, a surjective isometry, or a nonzero leakage coefficient.
- Distinguish algebraic polynomial, finite compressed, formal-series, and analytic constructions. Finite dimension does not imply nilpotency.

## Multi-Agent Orchestration & Model Hierarchy (Phases A–B–C)

To maximize formalization throughput, maintain strict mathematical scrutiny, and prevent context saturation, chapter development follows an orchestrated multi-agent protocol with explicit model tiers:

1. **Model Tier Hierarchy:**
   - **Primary Workhorse (`flash`):** Default to Gemini 3.8 Flash (medium or high effort) for all subagents. Flash is the primary workhorse for initial file generation, drafting definitions, one-sorry theorem stubs, companion notebooks, routine tactic searches, and sectional proof construction.
   - **Troubleshooting Escalation (`pro`):** Escalate to Gemini 3.1 Pro **strictly as a second option** when Flash fails, encounters persistent elaboration errors, or remains blocked after 3 tactic attempts at an unchanged goal. `pro` is reserved for deep mathematical diagnosis, subtle semantic debugging, and auxiliary lemma decomposition.

2. **Phase A (Drafting & Interface Verification):**
   - The orchestrator spawns a subagent (`Model: "flash"`) to author the staging Lean file in `BosonizeStubs/` and the companion notebook in `docs/companion/BosonizeStubs/`. (Escalate to `pro` only if Flash fails on complex structural modeling).
   - The orchestrator independently proof-reads and verifies all statement claims, hypotheses, types, carriers, and non-vacuity witnesses against the natural language notes.
   - Once approved, the orchestrator freezes the stub interface via `stub_lock.py`, commits the baseline atomically, and advances to Phase B.

3. **Phase B (Sectional Proving & Integration):**
   - The orchestrator decomposes the chapter by section or theorem cluster and spawns multiple sectional subagents (`Model: "flash"`), typically one per section.
   - If a sectional subagent gets stuck on an unchanged goal after 3 attempts, escalate that specific goal to a troubleshooting subagent (`Model: "pro"`).
   - The orchestrator collects and integrates all sectional proofs, verifies strict locks, zero `sorry`, clean build, and valid axioms, and decides whether Phase B is complete.

4. **Phase C (Audit, Promotion & Pedagogical Sync):**
   - The orchestrator promotes the module to Core, updates locks, and spawns a subagent running `pedagogical-sync` (`Model: "flash"`) to update the markdown notes.
   - The orchestrator reviews the pedagogical diff, confirms `make lock-check`, and commits atomically.

## Phase A — Draft and document

1. **Subagent Delegation (`flash`):** Do not hand-author large stubs monolithicly in the main conversation. Spawn a dedicated subagent (`invoke_subagent` with `TypeName: "self"` or specialized agent, `Model: "flash"`) to draft the file. The subagent writes complete definitions, abbreviations, and instances in `BosonizeStubs/`; each theorem/lemma stub ends with exactly one `:= by sorry`. Definitions and instances must elaborate without placeholders. Check adopted imports, library signatures, and required local instances against the installed Lean/Mathlib. If the Flash subagent encounters intractable elaboration bugs or type-theoretic modeling hurdles, escalate to a `pro` subagent as a second option.
2. **Companion Notebook:** The drafting subagent creates the mirrored notebook in `docs/companion/BosonizeStubs/`. Include type choices, exact signatures, source paths, unresolved mathematical obligations, proposed helper dependencies, and the reason for each margin. Useful witness lemmas can be Phase A stubs; do not describe their statements or a build with placeholders as proved evidence.
3. **Orchestrator Proofreading & Audit:** The orchestrator (or an independent adversarial review subagent) proof-reads and strictly verifies the draft against the natural language notes:
   - Check source fidelity, carrier types, explicit hypotheses and their necessity, non-vacuity/witnesses, operator order/signs, grading/margins, and actual adjoints.
   - Verify that definitions and instances elaborate cleanly with `lake build`.
4. **Interface Lock & Transition:** Resolve deterministic findings. Once approved, establish the reviewed lock in `docs/spec/stub_locks.v2.json` using `python3 scripts/guards/stub_lock.py`, commit the baseline atomically, and proceed automatically to Phase B. Ask the user only when a substantive ambiguity requires their mathematical or scope decision.

## Phase B — Prove the approved statements

1. **Pre-flight Lock Check:** Before editing, run `python3 scripts/guards/stub_lock.py --check --strict` from the repository root and identify the chapter in `docs/spec/stub_locks.v2.json`. Never regenerate the baseline to conceal drift.
2. **Sectional Subagent Partitioning (`flash`):** Decompose the chapter into modular sections or theorem clusters. Spawn multiple sectional subagents (typically one per section/cluster) using `Model: "flash"` as the workhorse to construct proofs in parallel or dependency order.
3. **Strict Boundary Compliance:** Subagents edit only approved lemma/theorem proof bodies. Preserve names, hypotheses, conclusions, definitions, instances, imports, namespaces, options, and attributes. Local `have` proofs provide supporting steps inside those bodies. New top-level declarations or interface changes require a concrete diff, evidence, and independent review before a scoped lock amendment.
4. **Troubleshooting Escalation (`pro`):** After three unsuccessful tactic attempts at the exact same goal state, stop retrying that goal with Flash. Escalate the goal, attempted tactics, and compiler diagnostics to a troubleshooting subagent running `Model: "pro"` to isolate the missing Mathlib lemma or formulate an auxiliary decomposition.
5. **Verification, Integration & Completion Decision:** The orchestrator collects the sectional proofs, merges them into the staging file, and runs:
   - Strict lock verification: `python3 scripts/guards/stub_lock.py --check --strict`
   - Build: `lake build <StagingTarget>`
   - Axiom audit: `#print axioms` (verifying only standard axioms `Classical.choice`, `propext`, `Quot.sound`)
   - Completeness audit: confirm zero remaining `sorry` placeholders and zero warnings.
   The orchestrator updates the companion notebook with compiler results and proof evidence, commits atomically, and decides whether Phase B is fully satisfied to proceed to Phase C.

## Compiler inspection and retrieval

Read the relevant sections of [Lean MCP operations](references/lean_mcp.md) when developing proofs, interpreting MCP results, validating a chapter, or investigating a Lean tool failure. This reference specializes the tool workflow for Bosonize-Lean; it does not authorize a new phase, interface change, or server reconfiguration.

Prefer native Lean MCP calls when exposed: inspect goals/diagnostics, search locally, then use syntactic or semantic library search as appropriate. Confirm exact imports, signatures, implicit parameters, and instance requirements before adopting a result. A proposed helper name or search hit alone is not evidence that its contract fits the chapter.

If a tool fails or is not exposed, state the precise limitation and continue with the installed compiler/local sources. Keep scratch files outside guarded source directories and remove temporary project artifacts. Report tool exposure, successful calls, compiler results, proof completion, and axiom audits separately; scratch placeholders and a successful diagnostic call do not establish proof completion.

## Retry and lint handling

After three unsuccessful tactic attempts at the exact same goal state, stop retrying that goal. Preserve completed proofs, record the goal, attempted approaches, and missing mathematical step, and obtain an independent troubleshooting pass (escalating from `flash` to `pro`). Resume on a materially different supported approach. Ask the user only for unresolved mathematical or scope ambiguity; a tactic failure alone is not a human approval gate. An existing unproved staging stub may remain; do not introduce new placeholders into completed proofs or Core. Continue independent authorized work where possible.

Resolve warnings at their cause. Use `omit` for unused section assumptions when appropriate, or explicit binders with the intended mathematical hypotheses. Do not disable a linter, suppress a diagnostic, or change the warning threshold to obtain Core promotion. If a fix changes a locked signature/context, treat it as an interface correction requiring the existing review procedure; never patch frozen Core silently.

## Phase C — Audit, promote, and freeze

After Phase B passes all audit criteria, proceed automatically within the authorized chapter scope using [the promotion workflow](../../workflows/freeze_chapter.md). Require zero placeholders, zero warnings, and only the permitted standard axioms (`propext`, `Classical.choice`, `Quot.sound`) in freshly built theorem dependencies. Preserve definitions, statements, and namespaces during promotion; move the v2 entry by path, preserving hashes except the narrowly reviewed promotion import/context substitutions described in that workflow, and add the complete-source hash to `docs/spec/core_locks.json`.

Move the companion notebook and update the aggregators as the workflow specifies. Spawn a subagent running the repository [pedagogical-sync skill](../pedagogical-sync/SKILL.md) (`Model: "flash"`) to update the corresponding chapter note in `notes/md/` (or appendix section in `notes/appendices/`), preserving reference information and explaining the verified constructive mathematics in natural language. Require orchestrator review of that pedagogical diff and record its evidence in the companion before declaring Phase C complete. CI and `make lock-check` must pass both guards. `core_lock.py` freezes every byte of existing Core sources, including proofs. Commit the authorized migration before using a reference containing it as the next baseline; retain historical manifests. Do not infer proof completion from a guard or a build with `sorry`.
