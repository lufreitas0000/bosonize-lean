# Lean 4 Coding Conventions and Project Rules

## 1. Mathematical Strictness
* **No Limits or Unbounded Operators:** Every formalized statement must represent an exact identity between finite-dimensional or purely algebraic objects. Do not use analytical limits or topological approximations (`≈`).
* **Explicit Hypotheses:** Regime conditions (e.g., energy budget margins $K$, $N$, $m$) must be explicit statement hypotheses. Do not hide them.

## 2. Naming Conventions
* **Theorems/Lemmas:** Use `snake_case` (e.g., `card_lattice_band`, `umbral_heisenberg`). These are opaque proofs.
* **Definitions/Data:** Use `lowerCamelCase` (e.g., `bandFinset`, `discreteDeriv`). These are computable functions or data.
* **Types/Classes/Namespaces:** Use `UpperCamelCase` (e.g., `LambdaDual`, `Bosonize.Core`).

## 3. Anti-Vacuity (No Green-Washing)
* Never define an operator, set, or physical state as trivially `0`, `id`, `∅`, or `⊥` just to satisfy a theorem.
* Ensure key objects ship with non-degeneracy/witness lemmas to prove that the constrained subspaces (e.g., the energy budget) are physically satisfiable and not empty.

## 4. The Single-Sorry Contract (Staging)
* Files in `BosonizeStubs/` must contain completely elaborated `def` and `abbrev` blocks.
* Theorem and lemma signatures in `BosonizeStubs/` must terminate with exactly one `:= by sorry`. Do not leave trailing or intermediate `sorry` tokens inside partial definitions.

## 5. Core Completeness
* Files migrated to `Bosonize/Core/` must compile with zero warnings and zero `sorry` or `admit` tokens.
* The `#print axioms` output for any theorem must only reveal standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
