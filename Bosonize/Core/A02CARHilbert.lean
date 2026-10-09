module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Data.Finset.Sort

/-!
# A02: finite occupation Hilbert space and CAR contracts
Phase A: complete data, one-sorry review stubs. Polynomial forms and Wick words are deferred.
-/

@[expose] public section

namespace Bosonize.A02

open scoped BigOperators ComplexConjugate

abbrev Occupation (ι : Type*) := Finset ι

abbrev FockSpace (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  EuclideanSpace ℂ (Occupation ι)

noncomputable def occupationONB (ι : Type*) [Fintype ι] [DecidableEq ι] :
    OrthonormalBasis (Occupation ι) ℂ (FockSpace ι) :=
  EuclideanSpace.basisFun (Occupation ι) ℂ

noncomputable def occupationBasis (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Module.Basis (Occupation ι) ℂ (FockSpace ι) :=
  (occupationONB ι).toBasis

noncomputable def ket {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Occupation ι) : FockSpace ι := occupationBasis ι S

/-- Algebraic coordinate transport; the function carrier is not given a new Hilbert norm. -/
noncomputable def coordinates (ι : Type*) [Fintype ι] [DecidableEq ι] :
    FockSpace ι ≃ₗ[ℂ] (Occupation ι → ℂ) :=
  WithLp.linearEquiv 2 ℂ (Occupation ι → ℂ)

noncomputable def extendBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (images : Occupation ι → FockSpace ι) : Module.End ℂ (FockSpace ι) :=
  (occupationBasis ι).constr ℂ images

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Endomorphism multiplication is composition: the right factor acts first. -/
def commutator (A B : Module.End ℂ V) : Module.End ℂ V := A * B - B * A

def anticommutator (A B : Module.End ℂ V) : Module.End ℂ V := A * B + B * A

/-- Algebraic CAR assumptions; adjoints are deliberately a separate contract. -/
structure AlgebraicCAR (ι : Type*) [DecidableEq ι] (V : Type*)
    [AddCommGroup V] [Module ℂ V] where
  annihilation : ι → Module.End ℂ V
  creation : ι → Module.End ℂ V
  annihilation_car : ∀ i j, anticommutator (annihilation i) (annihilation j) = 0
  creation_car : ∀ i j, anticommutator (creation i) (creation j) = 0
  mixed_car : ∀ i j, anticommutator (annihilation i) (creation j) =
    (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ V)

def AlgebraicCAR.number {ι : Type*} [DecidableEq ι]
    (R : AlgebraicCAR ι V) (i : ι) : Module.End ℂ V :=
  R.creation i * R.annihilation i

variable {ι : Type*} [DecidableEq ι]

lemma car_bilinear_commutator (R : AlgebraicCAR ι V) (a b c d : ι) :
    commutator (R.creation a * R.annihilation b) (R.creation c * R.annihilation d) =
      (if b = c then (1 : ℂ) else 0) • (R.creation a * R.annihilation d) -
      (if a = d then (1 : ℂ) else 0) • (R.creation c * R.annihilation b) := by
  have hbc := R.mixed_car b c
  have hda := R.mixed_car d a
  have hac := R.creation_car a c
  have hbd := R.annihilation_car b d
  simp only [anticommutator] at hbc hda hac hbd
  unfold commutator
  calc
    _ = R.creation a * (R.annihilation b * R.creation c + R.creation c * R.annihilation b) * R.annihilation d -
        R.creation c * (R.annihilation d * R.creation a + R.creation a * R.annihilation d) * R.annihilation b -
        (R.creation a * R.creation c + R.creation c * R.creation a) * R.annihilation b * R.annihilation d +
        R.creation c * R.creation a * (R.annihilation b * R.annihilation d + R.annihilation d * R.annihilation b) := by noncomm_ring
    _ = _ := by rw [hbc, hda, hac, hbd]; simp [eq_comm]

lemma car_number_creation_commutator (R : AlgebraicCAR ι V) (i j : ι) :
    commutator (R.number i) (R.creation j) =
      (if i = j then (1 : ℂ) else 0) • R.creation j := by
  have h := R.mixed_car i j
  have hc := R.creation_car i j
  simp only [anticommutator] at h hc
  unfold commutator AlgebraicCAR.number
  calc
    _ = R.creation i * (R.annihilation i * R.creation j + R.creation j * R.annihilation i) -
        (R.creation i * R.creation j + R.creation j * R.creation i) * R.annihilation i := by noncomm_ring
    _ = _ := by
      rw [h, hc]
      by_cases hij : i = j
      · subst j; simp
      · simp [hij]

lemma car_number_annihilation_commutator (R : AlgebraicCAR ι V) (i j : ι) :
    commutator (R.number i) (R.annihilation j) =
      -(if i = j then (1 : ℂ) else 0) • R.annihilation j := by
  have h := R.mixed_car j i
  have ha := R.annihilation_car i j
  simp only [anticommutator] at h ha
  unfold commutator AlgebraicCAR.number
  calc
    _ = R.creation i * (R.annihilation i * R.annihilation j + R.annihilation j * R.annihilation i) -
        (R.annihilation j * R.creation i + R.creation i * R.annihilation j) * R.annihilation i := by noncomm_ring
    _ = _ := by
      rw [h, ha]
      by_cases hij : i = j
      · subst j; simp
      · simp [hij, Ne.symm hij]

lemma car_number_commute (R : AlgebraicCAR ι V) (i j : ι) :
    R.number i * R.number j = R.number j * R.number i := by
  have h := car_bilinear_commutator R i i j j
  simp only [AlgebraicCAR.number, commutator] at *
  by_cases hij : i = j
  · subst j; rfl
  · simpa [hij, Ne.symm hij, sub_eq_zero] using h

lemma car_number_idempotent (R : AlgebraicCAR ι V) (i : ι) :
    R.number i * R.number i = R.number i := by
  have hc : R.creation i * R.creation i = 0 := by
    have h : (2 : ℂ) • (R.creation i * R.creation i) = 0 := by
      simpa [anticommutator, two_smul] using R.creation_car i i
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have ha : R.annihilation i * R.annihilation i = 0 := by
    have h : (2 : ℂ) • (R.annihilation i * R.annihilation i) = 0 := by
      simpa [anticommutator, two_smul] using R.annihilation_car i i
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hm := R.mixed_car i i
  simp only [anticommutator, ite_true, one_smul] at hm
  unfold AlgebraicCAR.number
  calc
    _ = R.creation i * (R.annihilation i * R.creation i + R.creation i * R.annihilation i) * R.annihilation i -
        (R.creation i * R.creation i) * (R.annihilation i * R.annihilation i) := by noncomm_ring
    _ = _ := by rw [hm, hc, ha]; simp

end Algebraic

/-- Finite Hilbert CAR includes actual adjoint compatibility, not just algebraic relations. -/
structure CAR (ι : Type*) [DecidableEq ι] (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    extends AlgebraicCAR ι V where
  adjoint_compat : ∀ i, creation i = LinearMap.adjoint (annihilation i)

section Occupations

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma ket_apply (S T : Occupation ι) :
    ket S T = if T = S then (1 : ℂ) else 0 := by
  simp [ket, occupationBasis, occupationONB, EuclideanSpace.basisFun_apply, PiLp.single_apply, eq_comm]

lemma coordinates_ket (S T : Occupation ι) :
    coordinates ι (ket S) T = if T = S then (1 : ℂ) else 0 := by
  exact ket_apply S T

lemma ket_inner (S T : Occupation ι) :
    inner ℂ (ket S) (ket T) = if S = T then (1 : ℂ) else 0 := by
  change inner ℂ (EuclideanSpace.basisFun (Occupation ι) ℂ S) (ket T) = _
  rw [EuclideanSpace.basisFun_inner, ket_apply]

lemma ket_norm (S : Occupation ι) : ‖ket S‖ = 1 := by
  exact (occupationONB ι).orthonormal.norm_eq_one S

lemma ket_ne_zero (S : Occupation ι) : ket S ≠ 0 := by
  intro h
  have hn := ket_norm S
  rw [h, norm_zero] at hn
  norm_num at hn

lemma vacuum_ne_zero : ket (∅ : Occupation ι) ≠ 0 := by
  exact ket_ne_zero ∅

lemma fock_inner (u v : FockSpace ι) :
    inner ℂ u v = ∑ S : Occupation ι, conj (u S) * v S := by
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro S _
  exact mul_comm _ _

lemma occupation_expansion (v : FockSpace ι) :
    v = ∑ S : Occupation ι, v S • ket S := by
  simpa [ket, occupationBasis, occupationONB, EuclideanSpace.basisFun_repr] using
    ((occupationONB ι).sum_repr v).symm

lemma extend_basis_ket (images : Occupation ι → FockSpace ι) (S : Occupation ι) :
    extendBasis images (ket S) = images S := by
  exact (occupationBasis ι).constr_basis ℂ images S

lemma end_ext_basis (A B : Module.End ℂ (FockSpace ι))
    (h : ∀ S : Occupation ι, A (ket S) = B (ket S)) : A = B := by
  exact (occupationBasis ι).ext h

lemma adjoint_of_basis_pairing (A B : Module.End ℂ (FockSpace ι))
    (h : ∀ S T : Occupation ι, inner ℂ (ket S) (A (ket T)) =
      inner ℂ (B (ket S)) (ket T)) : B = LinearMap.adjoint A := by
  apply (LinearMap.eq_adjoint_iff B A).mpr
  intro u v
  rw [occupation_expansion u, occupation_expansion v]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  apply Finset.sum_congr rfl
  intro T _
  rw [← h T S]

lemma fock_finrank : Module.finrank ℂ (FockSpace ι) = 2 ^ Fintype.card ι := by
  simp [FockSpace, Occupation, Fintype.card_finset]

lemma empty_modes_finrank [IsEmpty ι] : Module.finrank ℂ (FockSpace ι) = 1 := by
  rw [fock_finrank]
  simp

end Occupations

end Bosonize.A02
