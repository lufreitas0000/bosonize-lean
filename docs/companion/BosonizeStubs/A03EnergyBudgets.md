# A03 companion notebook — coordinate budgets and filtered maps

Status (2026-10-09): **Phase A complete; unlocked and unproved, awaiting interface review.** Baseline: `509f323`, containing eight frozen Core modules and 271 proved lemmas. This draft has 19 complete data declarations and 47 theorem stubs. No locking or Phase B work is authorized by this draft.

## Source reconciliation and design choices

Read [A03](../../../notes/appendices/a03_energy_budgets_and_filtered_maps.md), [CH07](../../../notes/md/ch07_vacuum_budget_space.md), [TOC](../../../notes/md/TOC.md), [appendix index](../../../notes/appendices/README.md), the [proof revision guide](../../../note/proof_suggestions_revision_2026-10-09.md) P07/P08, and the restricted-map, grading, and witness sections of [proof design](../../../.agents/skills/formalizer/references/proof_design.md). Suggestion directories contain no available A03 or CH07 files. Old TOC/index claims that only CH01–CH02 are frozen are historical; the current Core has CH01–CH06, A01 and finite-CAR A02.

A03 supplies the reusable coordinate calculus; the chapter-specific integer charge, sea subtraction, sorted configurations and ground states live in CH07. This avoids a circular appendix/chapter import. The generic carrier is the actual finite occupation Hilbert space `A02.FockSpace ι` with `Fintype ι` and `DecidableEq ι`. It requires no artificial order on the mode type. `A02.extendBasis` constructs diagonal operators; coordinate spans are `Submodule.span ℂ (ket '' U)`. The projection uses the indicator of retained basis coordinates. These are complete definitions, without using unproved lemmas.

`budget charge energy N K` uses signed `K : ℤ`; negative budgets become zero only under the explicit hypothesis that the supplied energy function is nonnegative. Natural-cutoff extraction is a downstream operation. A03's generic charge and energy functions deliberately have no positivity assumption baked into their data. `fixedEnergy` and `chargeBox` distinguish an exact joint eigenspace, a fixed-sector upper cutoff, and an absolute-charge upper cutoff. Pairwise orthogonality and supremum decompositions describe their orthogonal direct-sum behavior without assuming a separate direct-sum basis.

`Filtered` requires every actual basis output to lie in the coordinate span with charge exactly shifted by q and energy bounded above by input energy+d. It has no hidden K parameter and implies maps for every signed budget. `ExactShift` has exact energy support and supplies the charge/energy observable commutators; an upper-bound shift alone does not imply the energy commutator. The identity witness is a theorem stub, not an assumed field of an operator structure. `restrictedMap` is an actual submodule-to-submodule linear map accepting an explicit image certificate. It does not manufacture that certificate from an unproved staging theorem.

Endomorphism multiplication acts right-to-left. `applicationWord [A,B]` evaluates to B*A because lists are in application order. `prefixShifts` scans signed shifts from zero; `upwardExcursion` takes the largest scanned value with zero included. Both `[2,-2]` and `[-2,2]` are explicit stub examples. `filtered_application_word` carries total charge/energy shifts, while `charge_preserving_word_prefix` bounds every actual prefix by the input cutoff plus maximum excursion. This latter wrapper requires q=0 for every step. Words that change charge require a separate intermediate charge-box bound; `wordCutoff` alone does not certify them.

The projection calculus retains `Ptarget*A*(1-Pmiddle)*B*Psource`. Equality is equivalent to its vanishing; preserving the intermediate image is a sufficient condition, not a required strengthening of every identity. The restricted adjoint reverses the projection side. `compress` is P*A*P on the ambient carrier, and its square differs from compressing A² by the explicit intermediate-escape term. No scalar finite-slice CCR is claimed. Polynomial oscillator constructions are deferred to CH08; these generic helpers state only the available coordinate/restriction calculus.

## Proposed Phase B dependency order and review obligations

1. Basis-coordinate support and diagonal action; span monotonicity, unions and orthogonality.
2. Indicator projections: basis action, range, fixed vectors, idempotence, actual adjoint and commuting intersections; nonzero projection witness.
3. Signed budgets and exact-energy/charge-box decompositions, with nonnegative-energy premises where needed.
4. Filtered basis action to budget maps and composition; exact-shift observable commutators; negative-output annihilation.
5. Typed restricted maps, adjoint reversal, compression and exact remainder identities.
6. Prefix excursion arithmetic and application-order word bounds.

Every proposed theorem remains a one-sorry stub. The upstream basis APIs and construction types elaborate, but this does not establish the listed identities. Local proof support can be introduced inside Phase B bodies; new top-level helper declarations would need reviewed interfaces. Source advice to clip a negative output cutoff to zero is adapted to signed budgets so that annihilation below zero is not lost. Multi-species total energy is instantiated in CH07 on the combined mode carrier, not modeled as independent per-species cutoffs.

## Validation and phase boundary

Direct compilation and staging build pass with exactly 47 expected sorry warnings and no other warnings/errors. Native Lean MCP diagnostics complete with success=true, partial=false, 47 sorry-category warnings, and no failed dependencies. All 19 data declarations have only standard axioms (or none); all 47 theorem stubs depend on sorryAx. Guard tests: 69 passed. Core build passed. Against `509f323`, non-strict interface verification preserves 271 statements/225 commands, and all eight Core source hashes remain unchanged. Strict verification rejects exactly A03 and CH07 as new unlocked files, as intended. Full strict CI is not reported as passing for these unreviewed drafts. Toolchain, dependency manifest, both lock manifests and Core aggregator remain unchanged.

The primary agent used the repository formalizer skill; no subagents were dispatched for this phase. Unrelated source edits and suggestion-file deletions are preserved outside this task. Review the generic signed-cutoff API, projection side/order and application-order convention before approving the interface lock and Phase B.

## Reviewed source provenance

| Reviewed source | SHA-256 |
| --- | --- |
| `notes/appendices/a03_energy_budgets_and_filtered_maps.md` | `95a46eb53d1144e787e458677be2f1014832e84df8a5e2c7113cbebb47fad83b` |
| `notes/md/ch07_vacuum_budget_space.md` | `54f2a5d89b7f220cf2c850c44587b2eb3d6952b00d26d141ea9b61772496d81b` |
| `notes/md/TOC.md` | `5ea6b32bdecf8f9c65a345dc12356ff767b176c0b131e32acdb836778b054977` |
| `notes/appendices/README.md` | `ce871fab4a58ecb41a2b99d4ad4b055bb55e400753249fa88edde45fd15ebcd9` |
| `note/proof_suggestions_revision_2026-10-09.md` | `1db5f28b3e392d3b400ccc219ac640778fc5ceabc5cba17dfeb44b225a1b383c` |
| `.agents/skills/formalizer/references/proof_design.md` | `4d4391b355f701cee468d726a4c165010a4aa82c67449ec00e8a221759db585b` |

## Fresh data and stub axiom output

```text
'Bosonize.A03.Operators' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.coordinateSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.coordinateProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.fixedEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.chargeBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.budgetProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.boxProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.Filtered' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.ExactShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.compress' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.restrictedMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.applicationWord' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.prefixShifts' does not depend on any axioms
'Bosonize.A03.upwardExcursion' does not depend on any axioms
'Bosonize.A03.positiveExcursion' depends on axioms: [propext]
'Bosonize.A03.uniformCutoff' does not depend on any axioms
'Bosonize.A03.wordCutoff' does not depend on any axioms
'Bosonize.A03.diagonal_ket' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.diagonal_adjoint' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.ket_mem_coordinate_space' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.coordinate_space_support' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.coordinate_space_mono' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.coordinate_space_empty' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.coordinate_space_univ' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.coordinate_space_union' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.coordinate_space_disjoint' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.projection_ket' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.projection_idempotent' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.projection_adjoint' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.projection_range' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.projection_fixed_iff' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.projection_intersection' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.projection_commute' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.projection_nonzero' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.budget_mono' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.box_mono' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.negative_budget' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.energy_spaces_orthogonal' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.budget_energy_decomposition' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.box_sector_decomposition' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.exact_shift_filtered' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.filtered_identity' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.filtered_budget_map' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.filtered_comp' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.filtered_lowering_zero' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.exact_shift_charge_commutator' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.exact_shift_energy_commutator' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.compression_maps' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.compression_adjoint' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.restricted_adjoint' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.compressed_square_remainder' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.restricted_map_apply' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.comp_agree' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.projection_product_remainder' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.projected_product_eq_iff' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.projected_product_eq_of_maps' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.excursion_nonneg' depends on axioms: [sorryAx]
'Bosonize.A03.prefix_le_excursion' depends on axioms: [sorryAx]
'Bosonize.A03.excursion_le_positive' depends on axioms: [propext, sorryAx]
'Bosonize.A03.excursion_up_down' depends on axioms: [sorryAx]
'Bosonize.A03.excursion_down_up' depends on axioms: [sorryAx]
'Bosonize.A03.word_cutoff_prefix' depends on axioms: [sorryAx]
'Bosonize.A03.filtered_application_word' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A03.charge_preserving_word_prefix' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## Exact Lean source snapshot

Module SHA-256: `b2946aa526a8955904c32ed809c58f415df6b56e09fd5d6ba653b1891599571a`. The block below matches the draft byte-for-byte and contains all exact signatures.

```lean
module

public import Bosonize.Core.A02CARHilbert

/-!
# A03: coordinate budgets and filtered maps
Phase A: complete constructions and one-sorry theorem contracts.
Signed integer cutoffs retain negative-energy annihilation and composition excursions.
-/

@[expose] public section

namespace Bosonize.A03

open scoped BigOperators Classical

section Coordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Operators (ι : Type*) [Fintype ι] [DecidableEq ι] := Module.End ℂ (A02.FockSpace ι)

noncomputable def coordinateSpace (U : Set (A02.Occupation ι)) : Submodule ℂ (A02.FockSpace ι) :=
  Submodule.span ℂ (A02.ket '' U)

noncomputable def diagonal (a : A02.Occupation ι → ℂ) : Operators ι :=
  A02.extendBasis (fun S => a S • A02.ket S)

noncomputable def coordinateProjection (U : Set (A02.Occupation ι)) : Operators ι := by
  classical
  exact diagonal (fun S => if S ∈ U then 1 else 0)

noncomputable def fixedEnergy (charge energy : A02.Occupation ι → ℤ) (N E : ℤ) :
    Submodule ℂ (A02.FockSpace ι) :=
  coordinateSpace {S | charge S = N ∧ energy S = E}

noncomputable def budget (charge energy : A02.Occupation ι → ℤ) (N K : ℤ) :
    Submodule ℂ (A02.FockSpace ι) :=
  coordinateSpace {S | charge S = N ∧ energy S ≤ K}

noncomputable def chargeBox (charge energy : A02.Occupation ι → ℤ) (K : ℤ) (Nmax : ℕ) :
    Submodule ℂ (A02.FockSpace ι) :=
  coordinateSpace {S | energy S ≤ K ∧ |charge S| ≤ (Nmax : ℤ)}

noncomputable def budgetProjection (charge energy : A02.Occupation ι → ℤ) (N K : ℤ) : Operators ι :=
  coordinateProjection {S | charge S = N ∧ energy S ≤ K}

noncomputable def boxProjection (charge energy : A02.Occupation ι → ℤ) (K : ℤ) (Nmax : ℕ) : Operators ι :=
  coordinateProjection {S | energy S ≤ K ∧ |charge S| ≤ (Nmax : ℤ)}

/-- Every input basis vector has output supported in the stated shifted coordinate set. -/
def Filtered (charge energy : A02.Occupation ι → ℤ) (A : Operators ι) (q d : ℤ) : Prop :=
  ∀ S, A (A02.ket S) ∈ coordinateSpace {T | charge T = charge S + q ∧ energy T ≤ energy S + d}

/-- Equality of the energy shift, for observable commutators rather than mere bounds. -/
def ExactShift (charge energy : A02.Occupation ι → ℤ) (A : Operators ι) (q d : ℤ) : Prop :=
  ∀ S, A (A02.ket S) ∈ coordinateSpace {T | charge T = charge S + q ∧ energy T = energy S + d}

noncomputable def compress (U : Set (A02.Occupation ι)) (A : Operators ι) : Operators ι :=
  coordinateProjection U * A * coordinateProjection U

lemma diagonal_ket (a : A02.Occupation ι → ℂ) (S : A02.Occupation ι) :
    diagonal a (A02.ket S) = a S • A02.ket S := by sorry

lemma diagonal_adjoint (a : A02.Occupation ι → ℂ) :
    LinearMap.adjoint (diagonal a) = diagonal (fun S => star (a S)) := by sorry

lemma ket_mem_coordinate_space (U : Set (A02.Occupation ι)) (S : A02.Occupation ι) :
    A02.ket S ∈ coordinateSpace U ↔ S ∈ U := by sorry

lemma coordinate_space_support (U : Set (A02.Occupation ι)) (v : A02.FockSpace ι) :
    v ∈ coordinateSpace U ↔ ∀ S, S ∉ U → A02.coordinates ι v S = 0 := by sorry

lemma coordinate_space_mono (U V : Set (A02.Occupation ι)) (hUV : U ⊆ V) :
    coordinateSpace U ≤ coordinateSpace V := by sorry

lemma coordinate_space_empty : coordinateSpace (∅ : Set (A02.Occupation ι)) = ⊥ := by sorry

lemma coordinate_space_univ : coordinateSpace (Set.univ : Set (A02.Occupation ι)) = ⊤ := by sorry

lemma coordinate_space_union (U V : Set (A02.Occupation ι)) :
    coordinateSpace (U ∪ V) = coordinateSpace U ⊔ coordinateSpace V := by sorry

lemma coordinate_space_disjoint (U V : Set (A02.Occupation ι)) (hUV : Disjoint U V) :
    ∀ u ∈ coordinateSpace U, ∀ v ∈ coordinateSpace V, inner ℂ u v = 0 := by sorry

lemma projection_ket (U : Set (A02.Occupation ι)) (S : A02.Occupation ι) :
    coordinateProjection U (A02.ket S) = if S ∈ U then A02.ket S else 0 := by sorry

lemma projection_idempotent (U : Set (A02.Occupation ι)) :
    coordinateProjection U * coordinateProjection U = coordinateProjection U := by sorry

lemma projection_adjoint (U : Set (A02.Occupation ι)) :
    LinearMap.adjoint (coordinateProjection U) = coordinateProjection U := by sorry

lemma projection_range (U : Set (A02.Occupation ι)) :
    LinearMap.range (coordinateProjection U) = coordinateSpace U := by sorry

lemma projection_fixed_iff (U : Set (A02.Occupation ι)) (v : A02.FockSpace ι) :
    coordinateProjection U v = v ↔ v ∈ coordinateSpace U := by sorry

lemma projection_intersection (U V : Set (A02.Occupation ι)) :
    coordinateProjection U * coordinateProjection V = coordinateProjection (U ∩ V) := by sorry

lemma projection_commute (U V : Set (A02.Occupation ι)) :
    coordinateProjection U * coordinateProjection V = coordinateProjection V * coordinateProjection U := by sorry

lemma projection_nonzero (U : Set (A02.Occupation ι)) (hU : U.Nonempty) :
    coordinateProjection U ≠ 0 := by sorry

lemma budget_mono (charge energy : A02.Occupation ι → ℤ) (N K K' : ℤ) (hK : K ≤ K') :
    budget charge energy N K ≤ budget charge energy N K' := by sorry

lemma box_mono (charge energy : A02.Occupation ι → ℤ) (K K' : ℤ) (Nmax Nmax' : ℕ)
    (hK : K ≤ K') (hN : Nmax ≤ Nmax') :
    chargeBox charge energy K Nmax ≤ chargeBox charge energy K' Nmax' := by sorry

lemma negative_budget (charge energy : A02.Occupation ι → ℤ)
    (he : ∀ S, 0 ≤ energy S) (N K : ℤ) (hK : K < 0) : budget charge energy N K = ⊥ := by sorry

lemma energy_spaces_orthogonal (charge energy : A02.Occupation ι → ℤ)
    (N E N' E' : ℤ) (hne : N ≠ N' ∨ E ≠ E') :
    ∀ u ∈ fixedEnergy charge energy N E, ∀ v ∈ fixedEnergy charge energy N' E',
      inner ℂ u v = 0 := by sorry

lemma budget_energy_decomposition (charge energy : A02.Occupation ι → ℤ)
    (he : ∀ S, 0 ≤ energy S) (N : ℤ) (K : ℕ) :
    budget charge energy N K = ⨆ E : Fin (K+1), fixedEnergy charge energy N (E.val : ℤ) := by sorry

lemma box_sector_decomposition (charge energy : A02.Occupation ι → ℤ) (K : ℤ) (Nmax : ℕ) :
    chargeBox charge energy K Nmax = ⨆ N : {N : ℤ // |N| ≤ (Nmax : ℤ)}, budget charge energy N.val K := by sorry

lemma exact_shift_filtered (charge energy : A02.Occupation ι → ℤ) (A : Operators ι) (q d : ℤ)
    (hA : ExactShift charge energy A q d) : Filtered charge energy A q d := by sorry

lemma filtered_identity (charge energy : A02.Occupation ι → ℤ) :
    Filtered charge energy (1 : Operators ι) 0 0 := by sorry

lemma filtered_budget_map (charge energy : A02.Occupation ι → ℤ) (A : Operators ι)
    (q d N K : ℤ) (hA : Filtered charge energy A q d) :
    ∀ v ∈ budget charge energy N K, A v ∈ budget charge energy (N+q) (K+d) := by sorry

lemma filtered_comp (charge energy : A02.Occupation ι → ℤ) (A B : Operators ι)
    (qA dA qB dB : ℤ) (hA : Filtered charge energy A qA dA) (hB : Filtered charge energy B qB dB) :
    Filtered charge energy (A*B) (qB+qA) (dB+dA) := by sorry

lemma filtered_lowering_zero (charge energy : A02.Occupation ι → ℤ)
    (he : ∀ S, 0 ≤ energy S) (A : Operators ι) (q d N K : ℤ)
    (hA : Filtered charge energy A q d) (hKd : K+d < 0) :
    ∀ v ∈ budget charge energy N K, A v = 0 := by sorry

lemma exact_shift_charge_commutator (charge energy : A02.Occupation ι → ℤ)
    (A : Operators ι) (q d : ℤ) (hA : ExactShift charge energy A q d) :
    A02.commutator (diagonal (fun S => (charge S : ℂ))) A = (q : ℂ) • A := by sorry

lemma exact_shift_energy_commutator (charge energy : A02.Occupation ι → ℤ)
    (A : Operators ι) (q d : ℤ) (hA : ExactShift charge energy A q d) :
    A02.commutator (diagonal (fun S => (energy S : ℂ))) A = (d : ℂ) • A := by sorry

lemma compression_maps (U : Set (A02.Occupation ι)) (A : Operators ι) :
    ∀ v ∈ coordinateSpace U, compress U A v ∈ coordinateSpace U := by sorry

lemma compression_adjoint (U : Set (A02.Occupation ι)) (A : Operators ι) :
    LinearMap.adjoint (compress U A) = compress U (LinearMap.adjoint A) := by sorry

lemma restricted_adjoint (P A B : Operators ι) (hP : LinearMap.adjoint P = P)
    (hAB : (A-B)*P = 0) : P*(LinearMap.adjoint A-LinearMap.adjoint B) = 0 := by sorry

lemma compressed_square_remainder (U : Set (A02.Occupation ι)) (A : Operators ι) :
    compress U (A^2) - (compress U A)^2 =
      coordinateProjection U*A*(1-coordinateProjection U)*A*coordinateProjection U := by sorry

end Coordinates

section Restricted
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- An actual linear map between submodule carriers, given its checked image condition. -/
def restrictedMap (U W : Submodule ℂ V) (A : Module.End ℂ V)
    (hA : ∀ v ∈ U, A v ∈ W) : U →ₗ[ℂ] W :=
  (A.domRestrict U).codRestrict W (fun v => hA v v.property)

/-- The list is in application order: [A,B] evaluates to B*A. -/
def applicationWord (As : List (Module.End ℂ V)) : Module.End ℂ V := As.reverse.prod

lemma restricted_map_apply (U W : Submodule ℂ V) (A : Module.End ℂ V)
    (hA : ∀ v ∈ U, A v ∈ W) (v : U) : (restrictedMap U W A hA v : V) = A v := by sorry

lemma comp_agree (U W : Submodule ℂ V) (A B C : Module.End ℂ V)
    (hC : ∀ v ∈ U, C v ∈ W) (hAB : ∀ w ∈ W, A w = B w) :
    ∀ v ∈ U, (A*C) v = (B*C) v := by sorry

lemma projection_product_remainder (Ptarget Pmiddle Psource A B : Module.End ℂ V) :
    Ptarget*A*B*Psource - Ptarget*A*Pmiddle*B*Psource =
      Ptarget*A*(1-Pmiddle)*B*Psource := by sorry

lemma projected_product_eq_iff (Ptarget Pmiddle Psource A B : Module.End ℂ V) :
    Ptarget*A*B*Psource = Ptarget*A*Pmiddle*B*Psource ↔
      Ptarget*A*(1-Pmiddle)*B*Psource = 0 := by sorry

lemma projected_product_eq_of_maps (Ptarget Pmiddle Psource A B : Module.End ℂ V)
    (hB : Pmiddle*B*Psource = B*Psource) :
    Ptarget*A*B*Psource = Ptarget*A*Pmiddle*B*Psource := by sorry

end Restricted

/-- Prefixes are listed in application order, beginning with the zero shift. -/
def prefixShifts (ds : List ℤ) : List ℤ := ds.scanl (· + ·) 0

def upwardExcursion (ds : List ℤ) : ℤ := (prefixShifts ds).foldl max 0

def positiveExcursion (ds : List ℤ) : ℤ := (ds.map (fun d => max d 0)).sum

def uniformCutoff (h M K Nmax : ℕ) : Prop := 2*M+K+Nmax ≤ h

def wordCutoff (h M K Nmax : ℕ) (ds : List ℤ) : Prop :=
  2*M+K+(upwardExcursion ds).toNat+Nmax ≤ h

lemma excursion_nonneg (ds : List ℤ) : 0 ≤ upwardExcursion ds := by sorry

lemma prefix_le_excursion (ds : List ℤ) (d : ℤ) (hd : d ∈ prefixShifts ds) :
    d ≤ upwardExcursion ds := by sorry

lemma excursion_le_positive (ds : List ℤ) : upwardExcursion ds ≤ positiveExcursion ds := by sorry

lemma excursion_up_down : upwardExcursion [2,-2] = 2 := by sorry

lemma excursion_down_up : upwardExcursion [-2,2] = 0 := by sorry

lemma word_cutoff_prefix (h M K Nmax : ℕ) (ds : List ℤ) (hw : wordCutoff h M K Nmax ds)
    (d : ℤ) (hd : d ∈ prefixShifts ds) :
    (2*M : ℤ)+(K : ℤ)+d+(Nmax : ℤ) ≤ (h : ℤ) := by sorry

section Words
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma filtered_application_word (charge energy : A02.Occupation ι → ℤ)
    (word : List (Operators ι × (ℤ × ℤ)))
    (hw : ∀ step ∈ word, Filtered charge energy step.1 step.2.1 step.2.2) :
    Filtered charge energy (applicationWord (word.map Prod.fst))
      (word.map (fun step => step.2.1)).sum (word.map (fun step => step.2.2)).sum := by sorry

lemma charge_preserving_word_prefix (charge energy : A02.Occupation ι → ℤ)
    (word : List (Operators ι × ℤ))
    (hw : ∀ step ∈ word, Filtered charge energy step.1 0 step.2)
    (N K : ℤ) (r : ℕ) :
    ∀ v ∈ budget charge energy N K,
      applicationWord ((word.take r).map Prod.fst) v ∈
        budget charge energy N (K+upwardExcursion (word.map Prod.snd)) := by sorry

end Words

end Bosonize.A03
```
