---
name: formalizer
description: Draft, prove, and audit Bosonize-Lean chapters with mirrored notebooks and frozen interfaces. Use for chapter formalization and review of proposed Lean definitions or proofs in this repository.
---

# Bosonize-Lean formalizer

Translate the project's 1+1D lattice field-theory notes into rigorous Lean 4. Follow the chapter dependency graph and [Lean conventions](../../rules/lean_conventions.md). Use the installed compiler as the authority for elaboration and proof checking; notes, appendices, and suggested code still need mathematical scrutiny.

Work within the user's authorized chapter and phase. Use approval already given in the conversation; a passing freeze guard alone does not authorize proof work or promotion. Preserve unrelated worktree edits and upstream locked Core sources.

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

## Phase A — Draft and document

Write complete definitions, abbreviations, and instances in `BosonizeStubs/`; each theorem/lemma stub ends with exactly one `:= by sorry`. Definitions and instances must elaborate without placeholders. Check adopted imports, library signatures, and required local instances against the installed Lean/Mathlib before freezing the interface.

Create the mirrored notebook in `docs/companion/BosonizeStubs/`. Include type choices, exact signatures, source/suggestion paths, unresolved mathematical obligations, proposed helper dependencies, and the reason for each margin. Useful witness lemmas can be Phase A stubs; do not describe their statements or a build with placeholders as proved evidence. If the chapter is already locked, preserve its approved interface rather than redrafting it. Present Phase A for human review before locking or entering Phase B unless that approval has already been supplied.

## Phase B — Prove the approved statements

Before editing, run `python3 scripts/guards/stub_lock.py --check --strict` from the repository root and identify the chapter in `docs/spec/stub_locks.v2.json`. Use `--baseline-ref <approved-ref>` when verifying against a committed baseline, or `STUB_LOCK_BASELINE_REF` for CI. Investigate a failed check; never regenerate the baseline to conceal drift.

Edit only approved lemma/theorem proof bodies. Preserve names, hypotheses, conclusions, definitions, instances, imports, namespaces, options, and attributes. Local `have` proofs can provide supporting steps inside those bodies. New top-level declarations/files or changes to a frozen interface require explicit review and baseline approval; propose their exact statements and purpose before extending the lock. Never rewrite existing Core to solve a downstream problem.

Revisiting unusual or redundant assumptions is an expected, healthy part of proof development. Check whether each assumption is necessary, satisfiable, and appropriate for downstream use. When compiler or mathematical evidence supports a cleaner frozen interface, present the exact correction for review, then update only the approved lock records and repeat validation. Use approval already given for that correction; proof completion does not by itself authorize an interface change.

Plan a dependency order from verified basis action, grading, and exact edge identities to restricted consequences. Check that proposed helper hypotheses are satisfiable and do not strengthen the locked target unnoticed. A suggested tactic failure is a reason to revise the proof strategy, not the frozen mathematics.

After a proof batch, rerun the strict guard, inspect the source/dependency diff, build the affected staging module, and update the notebook with compiler results and remaining placeholders. Separate passed compilation, proof completion, axiom auditing, and mathematical witness evidence in the report.

The v2 guard freezes theorem headers and ordered non-lemma commands in staging and Core; it does not elaborate Lean or freeze imported dependencies/toolchain state. `docs/spec/stub_locks.v2.json` is active; preserve the legacy manifest as history. See [the freeze audit](../../../docs/spec/freeze_audit.md) for guard details. Do not use `--accept-changes` without explicit authorization; `--update` is disabled in CI.

## Compiler inspection and retrieval

Read the relevant sections of [Lean MCP operations](references/lean_mcp.md) when developing proofs, interpreting MCP results, validating a chapter, or investigating a Lean tool failure. This reference specializes the tool workflow for Bosonize-Lean; it does not authorize a new phase, interface change, or server reconfiguration.

Prefer native Lean MCP calls when exposed: inspect goals/diagnostics, search locally, then use syntactic or semantic library search as appropriate. Confirm exact imports, signatures, implicit parameters, and instance requirements before adopting a result. A proposed helper name or search hit alone is not evidence that its contract fits the chapter.

If a tool fails or is not exposed, state the precise limitation and continue with the installed compiler/local sources. Keep scratch files outside guarded source directories and remove temporary project artifacts. Report tool exposure, successful calls, compiler results, proof completion, and axiom audits separately; scratch placeholders and a successful diagnostic call do not establish proof completion.

## Retry and lint handling

After three unsuccessful tactic attempts at the exact same goal state, stop retrying that goal. Preserve completed proofs, record the goal, attempted approaches, and missing mathematical step, and request a decomposition or guidance. An existing unproved staging stub may remain; do not introduce new placeholders into completed proofs or Core. Continue independent authorized work where possible.

Resolve warnings at their cause. Use `omit` for unused section assumptions when appropriate, or explicit binders with the intended mathematical hypotheses. Do not disable a linter, suppress a diagnostic, or change the warning threshold to obtain Core promotion. If a fix changes a locked signature/context, treat it as an interface correction requiring the existing review procedure; never patch frozen Core silently.

## Phase C — Audit, promote, and freeze

After authorization, follow [the promotion workflow](../../workflows/freeze_chapter.md). Require zero placeholders, zero warnings, and only the permitted standard axioms (`propext`, `Classical.choice`, `Quot.sound`) in freshly built theorem dependencies. Preserve definitions, statements, and namespaces during promotion; move the v2 entry by path without changing its hashes and add the complete-source hash to `docs/spec/core_locks.json`.

Move the companion notebook and update the aggregators as the workflow specifies. CI and `make lock-check` must pass both guards. `core_lock.py` freezes every byte of existing Core sources, including proofs. Commit the authorized migration before using a reference containing it as the next baseline; retain historical manifests. Do not infer proof completion from a guard or a build with `sorry`.
