---
name: formalizer
description: Draft, prove, and audit Bosonize-Lean chapters with mirrored notebooks and frozen interfaces. Use for chapter formalization and review of proposed Lean definitions or proofs in this repository.
---

# Bosonize-Lean formalizer

Translate the project's 1+1D lattice field-theory notes into rigorous Lean 4. Follow the chapter dependency graph and [Lean conventions](../../rules/lean_conventions.md). Use the installed compiler as the authority for elaboration and proof checking; notes, appendices, and suggested code still need mathematical scrutiny.

For authorized chapter development, follow the repository's automatic A–B–C policy: independently review Phase A, establish the reviewed lock, prove in Phase B, then audit/promote/freeze in Phase C without routine human confirmation. Read [Pipeline and independent review](references/pipeline.md) for transition criteria, reviewer duties, interface corrections and escalation. Honor an explicit instruction to stop at a particular phase or only review/update the workflow. Do not select further chapters beyond the authorized scope. Preserve unrelated worktree edits and upstream locked Core sources.

## Usage allowance and checkpoints

Check live Codex usage before chapters, phase transitions and parallel proof groups, and approximately every 5–10 minutes during sustained work. If less than 10% of the five-hour allowance or less than 5% of the weekly allowance remains, warn, stop new proof work, save a resumable checkpoint and yield with a recommendation to pause. Follow [Usage allowance and resumable checkpoints](references/usage_budget.md) for tool availability, shared-account limits, delegated work and resumption. This guard can defer an otherwise automatic A–B–C transition; it never relaxes proof or freeze requirements. When the user explicitly authorizes autonomous quota resumption, schedule a thread wakeup after the limiting reset and recheck live allowance before restarting; do not spend reset credits. A whole-project request authorizes sequential roadmap items, while every chapter retains its independent review and validation gates.

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

## External workers and human browser operation

The default is a bounded external worker through `agentctl` or a human-operated
browser packet. Prefer Jules for suitable repository/document patches and eligible
OpenAI API pools for generation/review. Browser ChatGPT/Gemini/other chats can return
the same packet envelope; the local compiler and preservation gates decide acceptance.
No worker needs direct access to local credentials or the user's Lean installation.

Do not spawn desktop/Antigravity subagents or use headless Antigravity as the default
author/reviewer/fallback. `orchestrator/config/execution.toml` disables that backend.
Exhausted budgets checkpoint/defer work rather than moving it into a subscription
credit pool. Human browser usage is recorded as self-reported, not as API billing.
The supervising agent coordinates exceptions instead of rewriting every worker result.

One task owns each output. Review comes from an independent chat/worker; preserve
required review/adjudication gates and exact source identities. Prefer targeted
repairs and bounded dependency batches. `make work` is the human front door;
`make lean-check N LEAN_PHASE=B` checks a chapter response without approval or merge.
Existing finish commands remain explicit human approval/integration actions.

## Phase A — Draft and document

1. **External drafting:** Prepare a bounded Phase A packet for Jules, an eligible API worker, or the human browser route. Return complete definitions and one-sorry theorem stubs plus the companion. Check signatures and non-vacuity locally before freezing. Do not hand-author large monolithic drafts in the supervising conversation merely because a provider is unavailable.
2. **Companion Notebook:** The external drafting worker creates the mirrored notebook in `docs/companion/BosonizeStubs/`. Include type choices, exact signatures, source paths, unresolved mathematical obligations, proposed helper dependencies, and the reason for each margin. Useful witness lemmas can be Phase A stubs; do not describe their statements or a build with placeholders as proved evidence.
3. **Orchestrator Proofreading & Audit:** The orchestrator (or an independent external reviewer) proof-reads and strictly verifies the draft against the natural language notes:
   - Check source fidelity, carrier types, explicit hypotheses and their necessity, non-vacuity/witnesses, operator order/signs, grading/margins, and actual adjoints.
   - Verify that definitions and instances elaborate cleanly with `lake build`.
4. **Interface Lock & Transition:** Resolve deterministic findings. Once approved, establish the reviewed lock in `docs/spec/stub_locks.v2.json` using `python3 scripts/guards/stub_lock.py`, commit the baseline atomically, and proceed automatically to Phase B. Ask the user only when a substantive ambiguity requires their mathematical or scope decision.

## Phase B — Prove the approved statements

1. **Pre-flight Lock Check:** Before editing, run `python3 scripts/guards/stub_lock.py --check --strict` from the repository root and identify the chapter in `docs/spec/stub_locks.v2.json`. Never regenerate the baseline to conceal drift.
2. **Bounded proof batches:** Partition approved contracts into dependency-aware external tasks; one author per output. Human browser responses and API/Jules results pass the same statement, compiler and axiom gates. Preserve successful fragments; do not duplicate active workers.
3. **Strict Boundary Compliance:** Workers edit only approved lemma/theorem proof bodies. Preserve names, hypotheses, conclusions, definitions, instances, imports, namespaces, options, and attributes. Local `have` proofs provide supporting steps inside those bodies. New top-level declarations or interface changes require a concrete diff, evidence, and independent review before a scoped lock amendment.
4. **Bounded troubleshooting:** After three unsuccessful attempts at an unchanged goal, preserve the goal, candidate and complete compiler feedback. Request a targeted independent external diagnosis within the task budget; otherwise checkpoint and defer. A new paid/desktop fallback requires explicit authorization.
5. **Verification, Integration & Completion Decision:** The orchestrator collects the accepted proof batches, merges them into the staging file, and runs:
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

After three unsuccessful tactic attempts at the exact same goal state, stop retrying that goal. Preserve completed proofs, record the goal, attempted approaches, and missing mathematical step, and obtain an independent troubleshooting pass through a bounded external task. Resume on a materially different supported approach. Ask the user only for unresolved mathematical or scope ambiguity; a tactic failure alone is not a human approval gate. An existing unproved staging stub may remain; do not introduce new placeholders into completed proofs or Core. Continue independent authorized work where possible.

Resolve warnings at their cause. Use `omit` for unused section assumptions when appropriate, or explicit binders with the intended mathematical hypotheses. Do not disable a linter, suppress a diagnostic, or change the warning threshold to obtain Core promotion. If a fix changes a locked signature/context, treat it as an interface correction requiring the existing review procedure; never patch frozen Core silently.

## Phase C — Audit, promote, and freeze

After Phase B passes all audit criteria, proceed automatically within the authorized chapter scope using [the promotion workflow](../../workflows/freeze_chapter.md). Require zero placeholders, zero warnings, and only the permitted standard axioms (`propext`, `Classical.choice`, `Quot.sound`) in freshly built theorem dependencies. Preserve definitions, statements, and namespaces during promotion; move the v2 entry by path, preserving hashes except the narrowly reviewed promotion import/context substitutions described in that workflow, and add the complete-source hash to `docs/spec/core_locks.json`.

Move the companion notebook and update the aggregators as the workflow specifies. Assign an external worker following the repository [pedagogical-sync skill](../pedagogical-sync/SKILL.md) to update the corresponding chapter note in `notes/md/` (or appendix section in `notes/appendices/`), preserving reference information and explaining the verified constructive mathematics in natural language. Require orchestrator review of that pedagogical diff and record its evidence in the companion before declaring Phase C complete. CI and `make lock-check` must pass both guards. `core_lock.py` freezes every byte of existing Core sources, including proofs. Commit the authorized migration before using a reference containing it as the next baseline; retain historical manifests. Do not infer proof completion from a guard or a build with `sorry`.
