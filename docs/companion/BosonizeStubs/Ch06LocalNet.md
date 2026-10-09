# CH06 companion notebook — finite local CAR net

Status: **Phase A draft for human review**. This file mirrors `BosonizeStubs/Ch06LocalNet.lean`: 26 complete definitions/abbreviations and 54 unproved lemma contracts. No theorem has entered Phase B; no interface or complete-source lock is added by this draft.

## Source reconciliation and scope

The principal source is `notes/md/ch06_lattice_AQFT_net.md`, read with `notes/md/TOC.md`, the finite-CAR appendix `notes/appendices/a02_car_hilbert_and_normal_ordering.md`, the applicable source-contract and noncommutative sections of `.agents/skills/formalizer/references/proof_design.md`, and the dated review `note/proof_suggestions_revision_2026-10-09.md`. The completion ledger `note/notes_review_completion_2026-10-09.md` supplies review context, not Lean proofs. The TOC introductory claim that only CH01–CH02 are frozen is historical and superseded by the current Core and adaptive roadmap.

No `docs/stub_suggestion/` or `docs/proof_suggestion/` directory exists at this checkout snapshot. The source strategies are therefore adopted or adapted directly, subject to the contracts below. Source prose is not treated as proof.

| Input snapshot | SHA-256 |
| --- | --- |
| `notes/md/ch06_lattice_AQFT_net.md` | `2fc657d30296f423f1b4901442f9696053a445f5c2e5cc394bd7aea10c96ed39` |
| `notes/appendices/a02_car_hilbert_and_normal_ordering.md` | `1dfcf6960585d2871bfa92a305d299f94f5880d93775ae0e64d121ec46b55556` |
| `note/proof_suggestions_revision_2026-10-09.md` | `1db5f28b3e392d3b400ccc219ac640778fc5ceabc5cba17dfeb44b225a1b383c` |
| `note/notes_review_completion_2026-10-09.md` | `ee96609b0c32346be604041a99e3345c3420b71c830c88ef83ff8d93bd9c1dc1` |
| `BosonizeStubs/Ch05Fermions.lean` | `4433a21d4e418c9c745b213317e736425ccea1febbab527c34f429060d772446` |
| `Bosonize/Core/A02CARHilbert.lean` | `a683eaba06548c89167592302dc2e6b7f558a53e3acf50c5ff1cceffaeff16e3` |
| `Bosonize/Core/Ch04CARFock.lean` | `8be8dacb9212e7535e1fa7357398bb5b6a7cae6188d6d8643be6548d0ec422e0` |

The CH05 hash records the parallel draft used for elaboration; CH05 is not frozen or proved. CH06 depends on its position operators, inverse Fourier contracts, CAR, adjoint, and parity targets. Parallel Phase A is possible because those types are available now. Future CH06 proof development must respect the approved CH05 interface and dependency order rather than assume its stubs have been proved.

## Carriers and complete definitions

The carrier is exactly `Ch05.FockSpace L = A02.FockSpace (Ch01.Band L)`, with its existing Euclidean occupation basis. Operators are `Module.End ℂ` on this carrier. Regions are arbitrary `Set (Ch01.Lattice L)`; `[NeZero L]` guarantees a finite positive lattice for all position/local contracts. Nineteen purely momentum/parity/projection/matrix-unit contracts explicitly omit the unnecessary section instance before freezing; their complete definitions already work at every natural L. No positive-even assumption is needed for these net contracts. There are no energy budgets, sea shifts, infinite limits, extra physical AQFT axioms, or polynomial/Wick carriers in this module.

`localGenerators` contains both position annihilators and position creators in the region. `localAlgebra` is their genuine unital `Algebra.adjoin ℂ`. Actual `star` is provided by the installed finite-dimensional linear-map instance, whose `LinearMap.star_eq_adjoint` identifies it with `LinearMap.adjoint`. Star closure is an obligation, not an implicit extra assumption. Empty-region bottom means scalar multiples of the identity, not the zero algebra.

`parityOperator` uses the frozen momentum occupation parity of CH04. `parityMap` is a complete linear conjugation map built by composing installed `LinearMap.mulLeft` and `LinearMap.mulRight`. Its involution, multiplicativity, star compatibility, and ambient/local algebra automorphism upgrades are all lemma stubs. No definition fills an automorphism field with an unproved theorem.

The degree type is `Fin 2`, with sign `(-1 : ℂ)^σ.val`. `localPart I σ` intersects the local algebra's underlying submodule with `ker (parityMap - degreeSign σ • id)`. `evenPart` and `oddPart` are complete submodules; even and odd projections are `(id ± parityMap)/2`. The existence of a `Subalgebra` having the even submodule as its underlying module is an explicit target. An odd unital subalgebra is rejected: odd times odd is even. The nonempty-region proper-even statement has a proposed nonzero odd annihilator witness; the empty region has separate even-equals-full and odd-zero contracts.

Letters are pairs `(position, Bool)`, where `true` is a creator. `wordOperator` uses `List.prod`, so the rightmost factor acts first. `supportedWord` checks every letter position belongs to the specified region. `homogeneousWordSpan` is the span of supported words whose length modulo 2 equals the degree. An empty word represents the identity and belongs only to the even degree. This construction keeps arbitrary homogeneous sums available for locality; ordinary adjoin induction alone would lose that invariant.

## Ordered momentum matrix units and signs

Global fullness is based on the original **momentum** occupation basis. The module first asks that inverse Fourier recover every momentum annihilator and creator inside the position-generated global algebra. Position labels are never substituted for momentum occupation labels without that bridge.

`creatorWord S` is the **descending written product** of momentum creators; its ascending sequence of actions on the vacuum accumulates preceding counts `0,1,…,|S|−1`. Therefore `creatorSign S = (-1)^(|S|(|S|−1)/2)`. The annihilator word is the ascending written product, exactly the adjoint of the creator word. For two ordered occupied modes, descending creators have coefficient `−1`; ascending written creators instead have coefficient `+1`. A draft order/sign mismatch was corrected during Phase A review, before delivery. No constant-sign guess or commutative endomorphism product was adopted.

The vacuum projector is the fixed ascending ordered product of `1 - Ch04.number k` over every momentum mode. Its basis action, idempotence, and global membership remain unproved obligations.

`matrixUnit S T` is independently defined by genuine basis extension, sending ket `T` to ket `S` and all other basis vectors to zero. `orderedMatrixUnit S T` is the sign-corrected creator/projector/annihilator product. The correction multiplies by `creatorSign S * creatorSign T`; both signs square to one, so no unproved nonzero denominator is hidden. The equality between these two complete constructions is a theorem target. The expansion of an arbitrary operator uses its actual occupation coordinates, providing a direct span route to global fullness without guessing a dimension equality.

## Proposed lemma inventory and dependency order

All exact signatures appear in the source snapshot below. The 54 unproved contracts are grouped here to make their obligations reviewable.

| Group | Lemmas | Planned dependencies and unresolved obligations |
| --- | --- | --- |
| Local generation | `annihilation_mem_local`, `creation_mem_local`, `local_algebra_mono`, `local_algebra_union`, `local_algebra_empty`, `local_algebra_empty_scalar`, `local_algebra_star_closed`, `operator_star_eq_adjoint` | Installed adjoin Galois connection, scalar-image bottom, CH05 actual adjoints, and reversed-product star induction. |
| Parity action | `parity_map_apply`, `parity_map_involutive`, `parity_map_mul`, `parity_map_one`, `parity_map_star`, `parity_automorphism_exists`, `parity_annihilation`, `parity_creation`, `parity_preserves_local`, `local_parity_automorphism_exists` | CH04 parity square/adjoint; CH05 generator anticommutation with parity; local induction and restricted bijectivity. |
| Grading | `mem_local_part`, `even_subalgebra_exists`, `local_grading_sup`, `local_grading_disjoint`, `even_projection_mem`, `odd_projection_mem`, `projection_decomposition`, `even_projection_idempotent`, `odd_projection_idempotent`, `mixed_projections_zero`, `graded_mul`, `graded_star`, `even_part_empty`, `odd_part_empty` | Linear eigenspace identities, division by two over ℂ, involution, multiplication/star preservation. Establish the even algebra structure; never call the odd submodule an algebra. |
| Non-vacuity | `annihilation_nonzero`, `local_even_proper`, `local_odd_witness` | Position mixed CAR or adjoint/nonzero creation evidence from CH05; show the proposed witness is both odd and nonzero. |
| Words and locality | `word_mem_local`, `word_homogeneous`, `local_part_eq_word_span`, `disjoint_word_swap`, `twisted_locality`, `even_locality` | First identify the entire adjoin with word spans; use parity projections to extract homogeneous spans. Distinct generators from disjoint supports anticommute by all CH05 CAR cases; swap words with exact length-product sign, then extend bilinearly. |
| Global fullness | `momentum_annihilation_mem_global`, `momentum_creation_mem_global`, `creator_sign_square`, `creator_word_vacuum`, `annihilator_word_adjoint`, `vacuum_projector_ket`, `vacuum_projector_idempotent`, `vacuum_projector_mem_global`, `matrix_unit_ket`, `ordered_matrix_unit_eq`, `matrix_unit_mem_global`, `matrix_unit_expansion`, `global_algebra_eq_top` | Inverse Fourier before momentum generators; CH04 basis action and sorted products; exact CAR signs; Euclidean basis coordinates and finite double sums. |

Disjointness is the exact locality hypothesis; there are no budget margins or hidden AQFT assumptions. Full global CAR algebra is a target, not a property assumed by a structure. The local net is not replaced by `⊤`, and its even/odd objects are not defined as trivial zero spaces to force statements.

## Validation evidence — 2026-10-09

- `lake build BosonizeStubs.Ch06LocalNet` completed successfully against the parallel CH05 draft. The CH06 source has exactly **54 expected `sorry` warnings**, with no errors or linter warnings.
- Native Lean MCP `lean_diagnostic_messages` on the final source completed with `success: true`, `partial: false`, and exactly 54 diagnostics, all category `sorry`. This establishes diagnostic/LSP access and source elaboration, not proof completion.
- Fresh `#print axioms` on **all 26 complete definitions/abbreviations** reports only subsets of `propext`, `Classical.choice`, and `Quot.sound`; **none depends on `sorryAx`**. The complete audit output is preserved below; the transient command log was `/tmp/ch06-definition-audit.log`.
- Fresh `#print axioms` on all **54 lemma stubs** reports `sorryAx` in each, as expected for Phase A. Recorded output: `/tmp/ch06-stub-audit.log`. Those declarations are proposed contracts, not proved results.
- Joint parent validation passed both library builds and all 69 guard tests. Non-strict interface verification preserved all 182 approved statements and 152 commands, and the Core guard preserved all six existing source hashes. Strict verification rejected exactly the two new unreviewed CH05/CH06 files, as required in Phase A.
- No lock manifest, Core source, server configuration, source note, or unrelated deleted documentation was changed by this chapter drafting task. The parent task records combined aggregator, guard, and Git evidence separately.
- The mirrored Lean block below is byte-for-byte identical to the module at this snapshot. SHA-256: `6f81f26839d7d954d7c51fef50bf4eddf10d1876e1dde33fe7c58e5227a3ed9a`.

### Complete definition/abbreviation axiom audit

```text
'Bosonize.Ch06.FockSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.Operators' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.Region' does not depend on any axioms
'Bosonize.Ch06.Occupation' depends on axioms: [propext, Quot.sound]
'Bosonize.Ch06.Degree' does not depend on any axioms
'Bosonize.Ch06.Letter' does not depend on any axioms
'Bosonize.Ch06.localGenerators' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.localAlgebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.parityOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.parityMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.degreeSign' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.localPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.evenPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.oddPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.evenProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.oddProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.letterOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.wordOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.supportedWord' does not depend on any axioms
'Bosonize.Ch06.homogeneousWordSpan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.creatorWord' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.annihilatorWord' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.creatorSign' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.vacuumProjector' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.matrixUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.orderedMatrixUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Human review and explicit approval are required before freezing this interface or replacing any theorem stubs in Phase B.

## Exact Lean source snapshot

```lean
module

public import BosonizeStubs.Ch05Fermions
public import Bosonize.Core.Ch04CARFock
public import Mathlib.Algebra.Algebra.Operations

/-!
# CH06: finite local CAR net
Phase A review draft: complete data and one-sorry theorem contracts.
The grading is constructed linearly; no definition uses an unproved contract.
-/

@[expose] public section

namespace Bosonize.Ch06

open scoped BigOperators

abbrev FockSpace (L : ℕ) := Ch05.FockSpace L
abbrev Operators (L : ℕ) := Ch05.Operators L
abbrev Region (L : ℕ) := Set (Ch01.Lattice L)
abbrev Occupation (L : ℕ) := A02.Occupation (Ch01.Band L)
abbrev Degree := Fin 2
abbrev Letter (L : ℕ) := Ch01.Lattice L × Bool

variable (L : ℕ) [NeZero L]

/-- Both annihilation and creation are included before star closure is proved. -/
def localGenerators (I : Region L) : Set (Operators L) :=
  {A | ∃ x ∈ I, A = Ch05.positionAnnihilation L x ∨ A = Ch05.positionCreation L x}

noncomputable def localAlgebra (I : Region L) : Subalgebra ℂ (Operators L) :=
  Algebra.adjoin ℂ (localGenerators L I)

noncomputable def parityOperator : Operators L := Ch04.parity (ι := Ch01.Band L)

/-- Multiplication is composition, with the rightmost factor acting first. -/
noncomputable def parityMap : Operators L →ₗ[ℂ] Operators L :=
  (LinearMap.mulRight ℂ (parityOperator L)).comp (LinearMap.mulLeft ℂ (parityOperator L))

def degreeSign (σ : Degree) : ℂ := (-1 : ℂ) ^ σ.val

/-- Concrete eigenspaces; intersection keeps local membership explicit. -/
noncomputable def localPart (I : Region L) (σ : Degree) : Submodule ℂ (Operators L) :=
  (localAlgebra L I).toSubmodule ⊓
    LinearMap.ker (parityMap L - degreeSign σ • LinearMap.id)

noncomputable abbrev evenPart (I : Region L) : Submodule ℂ (Operators L) :=
  localPart L I 0

noncomputable abbrev oddPart (I : Region L) : Submodule ℂ (Operators L) :=
  localPart L I 1

noncomputable def evenProjection : Operators L →ₗ[ℂ] Operators L :=
  (2 : ℂ)⁻¹ • (LinearMap.id + parityMap L)

noncomputable def oddProjection : Operators L →ₗ[ℂ] Operators L :=
  (2 : ℂ)⁻¹ • (LinearMap.id - parityMap L)

/-- `true` denotes a creator and `false` an annihilator. -/
noncomputable def letterOperator (a : Letter L) : Operators L :=
  if a.2 then Ch05.positionCreation L a.1 else Ch05.positionAnnihilation L a.1

noncomputable def wordOperator (w : List (Letter L)) : Operators L :=
  (w.map (letterOperator L)).prod

def supportedWord (I : Region L) (w : List (Letter L)) : Prop :=
  ∀ a ∈ w, a.1 ∈ I

noncomputable def homogeneousWordSpan (I : Region L) (σ : Degree) :
    Submodule ℂ (Operators L) :=
  Submodule.span ℂ {A | ∃ w : List (Letter L), supportedWord L I w ∧
    w.length % 2 = σ.val ∧ A = wordOperator L w}

/-- Ordered products use the momentum occupation order, not spatial labels. -/
noncomputable def creatorWord (S : Occupation L) : Operators L :=
  (((S.sort (· ≤ ·)).reverse).map (Ch05.momentumCreation L)).prod

noncomputable def annihilatorWord (S : Occupation L) : Operators L :=
  ((S.sort (· ≤ ·)).map (Ch05.momentumAnnihilation L)).prod

/-- Descending creators act in ascending order, accumulating the triangular sign. -/
def creatorSign (S : Occupation L) : ℂ :=
  (-1 : ℂ) ^ (S.card * (S.card - 1) / 2)

noncomputable def vacuumProjector : Operators L :=
  (((Finset.univ : Finset (Ch01.Band L)).sort (· ≤ ·)).map
    (fun k => 1 - Ch04.number k)).prod

noncomputable def matrixUnit (S T : Occupation L) : Operators L :=
  A02.extendBasis fun U => if U = T then A02.ket S else 0

noncomputable def orderedMatrixUnit (S T : Occupation L) : Operators L :=
  (creatorSign L S * creatorSign L T) •
    (creatorWord L S * vacuumProjector L * annihilatorWord L T)

lemma annihilation_mem_local (I : Region L) (x : Ch01.Lattice L) (hx : x ∈ I) :
    Ch05.positionAnnihilation L x ∈ localAlgebra L I := by sorry

lemma creation_mem_local (I : Region L) (x : Ch01.Lattice L) (hx : x ∈ I) :
    Ch05.positionCreation L x ∈ localAlgebra L I := by sorry

lemma local_algebra_mono (I J : Region L) (hIJ : I ⊆ J) :
    localAlgebra L I ≤ localAlgebra L J := by sorry

lemma local_algebra_union (I J : Region L) :
    localAlgebra L (I ∪ J) = localAlgebra L I ⊔ localAlgebra L J := by sorry

lemma local_algebra_empty : localAlgebra L ∅ = ⊥ := by sorry

lemma local_algebra_empty_scalar (A : Operators L) :
    A ∈ localAlgebra L ∅ ↔ ∃ z : ℂ, A = z • (1 : Operators L) := by sorry

lemma local_algebra_star_closed (I : Region L) (A : Operators L)
    (hA : A ∈ localAlgebra L I) : star A ∈ localAlgebra L I := by sorry

omit [NeZero L] in
lemma operator_star_eq_adjoint (A : Operators L) :
    star A = LinearMap.adjoint A := by sorry

omit [NeZero L] in
lemma parity_map_apply (A : Operators L) :
    parityMap L A = parityOperator L * A * parityOperator L := by sorry

omit [NeZero L] in
lemma parity_map_involutive (A : Operators L) :
    parityMap L (parityMap L A) = A := by sorry

omit [NeZero L] in
lemma parity_map_mul (A B : Operators L) :
    parityMap L (A * B) = parityMap L A * parityMap L B := by sorry

omit [NeZero L] in
lemma parity_map_one : parityMap L 1 = 1 := by sorry

omit [NeZero L] in
lemma parity_map_star (A : Operators L) :
    parityMap L (star A) = star (parityMap L A) := by sorry

omit [NeZero L] in
/-- Automorphism structure is an obligation, not an assumed definition field. -/
lemma parity_automorphism_exists : ∃ α : Operators L ≃ₐ[ℂ] Operators L,
    (∀ A, α A = parityMap L A) ∧ ∀ A, α (star A) = star (α A) := by sorry

lemma parity_annihilation (x : Ch01.Lattice L) :
    parityMap L (Ch05.positionAnnihilation L x) = -Ch05.positionAnnihilation L x := by sorry

lemma parity_creation (x : Ch01.Lattice L) :
    parityMap L (Ch05.positionCreation L x) = -Ch05.positionCreation L x := by sorry

lemma parity_preserves_local (I : Region L) (A : Operators L)
    (hA : A ∈ localAlgebra L I) : parityMap L A ∈ localAlgebra L I := by sorry

lemma local_parity_automorphism_exists (I : Region L) :
    ∃ α : localAlgebra L I ≃ₐ[ℂ] localAlgebra L I,
      ∀ A, (α A : Operators L) = parityMap L (A : Operators L) := by sorry

lemma mem_local_part (I : Region L) (σ : Degree) (A : Operators L) :
    A ∈ localPart L I σ ↔ A ∈ localAlgebra L I ∧
      parityMap L A = degreeSign σ • A := by sorry

lemma even_subalgebra_exists (I : Region L) :
    ∃ E : Subalgebra ℂ (Operators L), E.toSubmodule = evenPart L I := by sorry

lemma local_grading_sup (I : Region L) :
    evenPart L I ⊔ oddPart L I = (localAlgebra L I).toSubmodule := by sorry

lemma local_grading_disjoint (I : Region L) :
    Disjoint (evenPart L I) (oddPart L I) := by sorry

lemma even_projection_mem (I : Region L) (A : Operators L)
    (hA : A ∈ localAlgebra L I) : evenProjection L A ∈ evenPart L I := by sorry

lemma odd_projection_mem (I : Region L) (A : Operators L)
    (hA : A ∈ localAlgebra L I) : oddProjection L A ∈ oddPart L I := by sorry

omit [NeZero L] in
lemma projection_decomposition (A : Operators L) :
    evenProjection L A + oddProjection L A = A := by sorry

omit [NeZero L] in
lemma even_projection_idempotent (A : Operators L) :
    evenProjection L (evenProjection L A) = evenProjection L A := by sorry

omit [NeZero L] in
lemma odd_projection_idempotent (A : Operators L) :
    oddProjection L (oddProjection L A) = oddProjection L A := by sorry

omit [NeZero L] in
lemma mixed_projections_zero (A : Operators L) :
    evenProjection L (oddProjection L A) = 0 ∧ oddProjection L (evenProjection L A) = 0 := by sorry

lemma graded_mul (I : Region L) (σ τ : Degree) (A B : Operators L)
    (hA : A ∈ localPart L I σ) (hB : B ∈ localPart L I τ) :
    A * B ∈ localPart L I (σ + τ) := by sorry

lemma graded_star (I : Region L) (σ : Degree) (A : Operators L)
    (hA : A ∈ localPart L I σ) : star A ∈ localPart L I σ := by sorry

lemma even_part_empty : evenPart L ∅ = (localAlgebra L ∅).toSubmodule := by sorry

lemma odd_part_empty : oddPart L ∅ = ⊥ := by sorry

lemma annihilation_nonzero (x : Ch01.Lattice L) :
    Ch05.positionAnnihilation L x ≠ 0 := by sorry

lemma local_even_proper (I : Region L) (hI : I.Nonempty) :
    evenPart L I < (localAlgebra L I).toSubmodule := by sorry

lemma local_odd_witness (I : Region L) (x : Ch01.Lattice L) (hx : x ∈ I) :
    Ch05.positionAnnihilation L x ∈ oddPart L I ∧
      Ch05.positionAnnihilation L x ≠ 0 := by sorry

lemma word_mem_local (I : Region L) (w : List (Letter L))
    (hw : supportedWord L I w) : wordOperator L w ∈ localAlgebra L I := by sorry

lemma word_homogeneous (w : List (Letter L)) :
    parityMap L (wordOperator L w) = (-1 : ℂ) ^ w.length • wordOperator L w := by sorry

/-- This contract supplies homogeneous sums; ordinary adjoin induction alone does not. -/
lemma local_part_eq_word_span (I : Region L) (σ : Degree) :
    localPart L I σ = homogeneousWordSpan L I σ := by sorry

lemma disjoint_word_swap (I J : Region L) (hIJ : Disjoint I J)
    (u v : List (Letter L)) (hu : supportedWord L I u) (hv : supportedWord L J v) :
    wordOperator L u * wordOperator L v =
      (-1 : ℂ) ^ (u.length * v.length) • (wordOperator L v * wordOperator L u) := by sorry

lemma twisted_locality (I J : Region L) (hIJ : Disjoint I J)
    (σ τ : Degree) (A B : Operators L)
    (hA : A ∈ localPart L I σ) (hB : B ∈ localPart L J τ) :
    A * B = (-1 : ℂ) ^ (σ.val * τ.val) • (B * A) := by sorry

lemma even_locality (I J : Region L) (hIJ : Disjoint I J) (A B : Operators L)
    (hA : A ∈ evenPart L I) (hB : B ∈ evenPart L J) :
    A02.commutator A B = 0 := by sorry

/-- The inverse Fourier bridge is required before momentum-basis matrix units. -/
lemma momentum_annihilation_mem_global (k : Ch01.Band L) :
    Ch05.momentumAnnihilation L k ∈ localAlgebra L Set.univ := by sorry

lemma momentum_creation_mem_global (k : Ch01.Band L) :
    Ch05.momentumCreation L k ∈ localAlgebra L Set.univ := by sorry

omit [NeZero L] in
lemma creator_sign_square (S : Occupation L) :
    creatorSign L S * creatorSign L S = 1 := by sorry

omit [NeZero L] in
lemma creator_word_vacuum (S : Occupation L) :
    creatorWord L S (A02.ket ∅) = creatorSign L S • A02.ket S := by sorry

omit [NeZero L] in
lemma annihilator_word_adjoint (S : Occupation L) :
    annihilatorWord L S = LinearMap.adjoint (creatorWord L S) := by sorry

omit [NeZero L] in
lemma vacuum_projector_ket (S : Occupation L) :
    vacuumProjector L (A02.ket S) = if S = ∅ then A02.ket ∅ else 0 := by sorry

omit [NeZero L] in
lemma vacuum_projector_idempotent :
    vacuumProjector L * vacuumProjector L = vacuumProjector L := by sorry

lemma vacuum_projector_mem_global :
    vacuumProjector L ∈ localAlgebra L Set.univ := by sorry

omit [NeZero L] in
lemma matrix_unit_ket (S T U : Occupation L) :
    matrixUnit L S T (A02.ket U) = if U = T then A02.ket S else 0 := by sorry

omit [NeZero L] in
lemma ordered_matrix_unit_eq (S T : Occupation L) :
    orderedMatrixUnit L S T = matrixUnit L S T := by sorry

lemma matrix_unit_mem_global (S T : Occupation L) :
    matrixUnit L S T ∈ localAlgebra L Set.univ := by sorry

omit [NeZero L] in
lemma matrix_unit_expansion (A : Operators L) :
    A = ∑ S : Occupation L, ∑ T : Occupation L,
      (A (A02.ket T)) S • matrixUnit L S T := by sorry

lemma global_algebra_eq_top : localAlgebra L Set.univ = ⊤ := by sorry

end Bosonize.Ch06
```
