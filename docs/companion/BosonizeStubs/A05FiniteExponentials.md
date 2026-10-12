# A05 — Generic exact finite exponentials (Phase A)

Source: [A05FiniteExponentials.lean](../../../BosonizeStubs/A05FiniteExponentials.lean).

This is a **review candidate**, not proved support. The definition is complete; thirteen theorem bodies are single-placeholder stubs. `lake build BosonizeStubs.A05FiniteExponentials` passed with exactly thirteen expected `sorry` warnings, zero errors and no other warnings. Independent review and a reviewed interface freeze must precede Phase B. Gemini Flash/Pro tools are not exposed; the available inherited Codex drafting agent is the recorded fallback.

## Source reconciliation and actual carriers

Source: [A05](../../../notes/appendices/a05_exponentials_klein_and_vertex_scope.md). Complete precedent: [CH08](../../../Bosonize/Core/Ch08Boson.lean), `taylor`, `expNil_cutoff`, `expNil_inverse` and `taylor_adjoint`. The generic definition acts on the supplied complex module itself. Endomorphism multiplication applies the right factor first. Degree d sums through d, so cutoff independence and inverse claims require the actual power A^(d+1)=0. Adjoint support additionally requires an actual finite-dimensional inner-product space. Finite dimensionality alone never certifies nilpotency.

The bounded filtration criterion explicitly requires a zero bottom, the actual whole-module top, and lowering of each prescribed level. No monotonicity assumption is needed for the iterative implication. Downstream compressed physical phases must prove those maps themselves. The criterion is nonvacuous: a two-coordinate square-zero shift admits the usual two-step kernel filtration. The nonzero-vector preservation contract retains its nonzero premise.

The expected `docs/stub_suggestion/` and `docs/proof_suggestion/` directories are absent in this checkout. Adopted: factorial coefficients and explicit nilpotency from Core CH08. Adapted: cutoff/inverse/adjoint proof plans to generic actual carriers. Rejected: input-budget K+1 nilpotency without a projection certificate, and any inference of a complete field–vertex identity from one ground coefficient. No convergence or formal-series assertion is made.

## Exact definition

```lean
noncomputable def finiteTaylor {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) : Module.End ℂ V :=
  ∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) • A ^ j
```

## Exact theorem candidates and proof plans

### `finite_taylor_zero_cutoff`

```lean
theorem finite_taylor_zero_cutoff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) : finiteTaylor 0 A = 1 := by sorry
```

Expand the singleton range and simplify factorial zero, scalar one and zeroth power.

### `finite_taylor_zero_operator`

```lean
theorem finite_taylor_zero_operator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) : finiteTaylor d (0 : Module.End ℂ V) = 1 := by sorry
```

Separate index zero; all strictly positive powers of zero vanish.

### `finite_taylor_apply`

```lean
theorem finite_taylor_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (v : V) :
    finiteTaylor d A v = ∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) • (A ^ j) v := by sorry
```

Distribute application across finite sums and scalar multiples.

### `finite_taylor_commute`

```lean
theorem finite_taylor_commute {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) : Commute A (finiteTaylor d A) := by sorry
```

Use commutation with every power, preserved by scalar multiples and sums.

### `finite_taylor_intertwine`

```lean
theorem finite_taylor_intertwine {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (d : ℕ) (A : Module.End ℂ V)
    (B : Module.End ℂ W) (T : V →ₗ[ℂ] W) (hT : T.comp A = B.comp T) :
    T.comp (finiteTaylor d A) = (finiteTaylor d B).comp T := by sorry
```

Induct on powers using hT, then distribute composition across the sum. Source and target remain actual distinct modules.

### `finite_taylor_cutoff`

```lean
theorem finite_taylor_cutoff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d e : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0) (hde : d ≤ e) :
    finiteTaylor e A = finiteTaylor d A := by sorry
```

Every extra power factors through A^(d+1)=0. Extend the range with proved zero terms; adapt Core CH08 cutoff.

### `finite_taylor_mul_neg`

```lean
theorem finite_taylor_mul_neg {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0) :
    finiteTaylor d A * finiteTaylor d (-A) = 1 := by sorry
```

Bridge to Mathlib IsNilpotent.exp by rational/complex factorial coefficient compatibility; use its actual nilpotent exponential inverse theorem. Adapt Core CH08 expNil_inverse.

### `finite_taylor_neg_mul`

```lean
theorem finite_taylor_neg_mul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0) :
    finiteTaylor d (-A) * finiteTaylor d A = 1 := by sorry
```

Apply the right inverse to -A and simplify double negation. Its same power vanishes.

### `finite_taylor_injective`

```lean
theorem finite_taylor_injective {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0) :
    Function.Injective (finiteTaylor d A) := by sorry
```

Apply and evaluate the explicit left inverse on equal images.

### `finite_taylor_surjective`

```lean
theorem finite_taylor_surjective {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0) :
    Function.Surjective (finiteTaylor d A) := by sorry
```

The negative polynomial supplies an explicit preimage by the right inverse identity.

### `finite_taylor_ne_zero`

```lean
theorem finite_taylor_ne_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0)
    (v : V) (hv : v ≠ 0) : finiteTaylor d A v ≠ 0 := by sorry
```

Use injectivity and preservation of zero to contradict the nonzero hypothesis.

### `finite_taylor_adjoint`

```lean
theorem finite_taylor_adjoint {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (d : ℕ) (A : Module.End ℂ V) :
    LinearMap.adjoint (finiteTaylor d A) = finiteTaylor d (LinearMap.adjoint A) := by sorry
```

Distribute actual adjoint through sums, real scalar coefficients and powers. Adapt Core CH08 taylor_adjoint; check finite-dimensional Hilbert instances.

### `filtration_nilpotent`

```lean
theorem filtration_nilpotent {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (F : ℕ → Submodule ℂ V)
    (hbottom : F 0 = ⊥) (htop : F (d + 1) = ⊤)
    (hlower : ∀ n ≤ d, ∀ v ∈ F (n + 1), A v ∈ F n) :
    A ^ (d + 1) = 0 := by sorry
```

Iteratively lower from the whole-module top to the zero bottom, then use endomorphism extensionality. Physical phases must independently prove every specified mapping condition.

## Completion gate

All thirteen theorem candidates remain unproved in Phase A. Nilpotency of the actual Chapter 14 phase operators is a separate obligation; neither it nor a physical field–vertex identity follows from this generic foundation. Require complete Phase B proofs, fresh standard-axiom audits, zero warnings/placeholders, strict guards and builds before promotion. The complementary A05 lecture update belongs to independently reviewed Phase C.

## Complete Phase B — 2026-10-12

All 37 combined theorem proofs and 20 data declarations are complete and freshly audited with only standard axioms; no placeholders or warnings remain. Both native diagnostic calls complete with empty items. The combined build passes 3405 jobs; strict guard verifies 793 statements and 632 commands. Independent final review records authorship and the root’s distinct review of the reviewer-authored eight proofs. Only the two previously reviewed scalar-instance omissions changed the frozen interface. Exact current source hashes and all 57 axiom reports are in note/ch14_phase_b_independent_audit_2026-10-12.json. Phase C promotion and complementary lecture review are next. Earlier Phase A status and placeholder counts are historical.
