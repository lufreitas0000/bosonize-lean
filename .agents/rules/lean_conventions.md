# Lean 4 Coding Conventions and Project Rules

## 1. Mathematical Strictness
* **Exact Algebraic Scope:** Every formalized statement must represent an exact identity between finite-dimensional or purely algebraic objects. Algebraic polynomial operators are permitted without asserting analytical boundedness or a Hilbert completion. Do not substitute analytical limits or topological approximations (`≈`) for exact identities.
* **Explicit Hypotheses:** Regime conditions (e.g., energy budget margins $K$, $N$, $m$) must be explicit statement hypotheses. Do not hide them.
* **Typed Restricted Action:** Track map sources/targets, operator order, adjoints, and projection remainders. Attach margins to the inputs where an identity is used; distinguish useful local conditions from stronger sufficient wrappers. Consult `.agents/skills/formalizer/references/proof_design.md` for the relevant mathematical contracts.

## 2. Naming Conventions
* **Theorems/Lemmas:** Use `snake_case` (e.g., `card_lattice_band`, `umbral_heisenberg`). These are opaque proofs.
* **Definitions/Data:** Use `lowerCamelCase` (e.g., `bandFinset`, `discreteDeriv`). These are computable functions or data.
* **Types/Classes/Namespaces:** Use `UpperCamelCase` (e.g., `LambdaDual`, `Bosonize.Core`).

## 3. Anti-Vacuity (No Green-Washing)
* Never define an operator, set, or physical state as trivially `0`, `id`, `∅`, or `⊥` just to satisfy a theorem.
* Ensure key objects ship with non-degeneracy/witness lemmas to prove that the constrained subspaces (e.g., the energy budget) are physically satisfiable and not empty.
* Where a claim uses a positive state, inverse map, or nonzero leakage action, establish that object's existence or the required coefficient. Nonempty budgets alone do not supply this evidence. Label proposed witness stubs separately from proved results.

## 4. The Single-Sorry Contract (Staging)
* Files in `BosonizeStubs/` must contain completely elaborated `def` and `abbrev` blocks.
* In Phase A, theorem and lemma signatures in `BosonizeStubs/` must terminate with exactly one `:= by sorry`. During authorized Phase B work, replace only their proof bodies with complete proofs. Do not leave trailing or intermediate `sorry` tokens inside partial definitions.

## 5. Core Completeness
* Files migrated to `Bosonize/Core/` must compile with zero warnings and zero `sorry` or `admit` tokens.
* Resolve warnings at their cause; do not suppress linters or lower warning thresholds for promotion. Use `omit` for unused section assumptions where appropriate. A change to a locked signature/context follows the interface-review procedure; existing Core stays frozen.
* The `#print axioms` output for any theorem must only reveal standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
* Complete Core sources, including proof bodies, are frozen by `scripts/guards/core_lock.py` against `docs/spec/core_locks.json`. CI and `make lock-check` run this guard as well as the v2 definition/statement guard. Never alter an existing Core source or its approved hash to solve downstream proof problems.

## 6. Approved Interface Preservation
* Run `python3 scripts/guards/stub_lock.py --check --strict` before and after Phase B proof batches. Never run `--update` to bypass a failed check; approved baseline changes require explicit human authorization.
* Preserve approved definitions, abbreviations, instances, declaration names, namespaces, hypotheses, and conclusions. The v2 guard freezes these commands and lemma headers in the guarded files. It does not freeze imported dependencies or toolchain state: review source and dependency diffs separately. A matching hash does not certify mathematical correctness or complete proofs.
* CI runs the guard tests and strict freeze verification before building. New declarations/files need review and baseline approval. Use an approved `--baseline-ref` (or CI variable `STUB_LOCK_BASELINE_REF`) to verify against a committed baseline rather than trusting a modified working-tree lock.

## 7. Critical Use of Suggestions
* Consult chapter-relevant `docs/stub_suggestion/` files when drafting interfaces and `docs/proof_suggestion/` files when planning and implementing proofs.
* Read chapter-relevant `notes/appendices/` and reconcile applicable review corrections with current source versions. Statements and sketches in the notes also require scrutiny; report false or underspecified claims instead of treating source prose as proof.
* Suggestions are unverified advisory material. Compare them with the reconciled source, check all hypotheses and non-vacuity conditions, and validate adopted code with the installed Lean compiler. Reject changes that weaken a claim, hide a domain restriction, or alter a frozen definition merely to accommodate a suggested proof.
* Record suggestion paths and adopted, adapted, or rejected ideas with reasons in the companion notebook.
