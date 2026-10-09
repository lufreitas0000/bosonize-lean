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
