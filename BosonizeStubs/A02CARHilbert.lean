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
      (if a = d then (1 : ℂ) else 0) • (R.creation c * R.annihilation b) := by sorry

lemma car_number_creation_commutator (R : AlgebraicCAR ι V) (i j : ι) :
    commutator (R.number i) (R.creation j) =
      (if i = j then (1 : ℂ) else 0) • R.creation j := by sorry

lemma car_number_annihilation_commutator (R : AlgebraicCAR ι V) (i j : ι) :
    commutator (R.number i) (R.annihilation j) =
      -(if i = j then (1 : ℂ) else 0) • R.annihilation j := by sorry

lemma car_number_commute (R : AlgebraicCAR ι V) (i j : ι) :
    R.number i * R.number j = R.number j * R.number i := by sorry

lemma car_number_idempotent (R : AlgebraicCAR ι V) (i : ι) :
    R.number i * R.number i = R.number i := by sorry

end Algebraic

/-- Finite Hilbert CAR includes actual adjoint compatibility, not just algebraic relations. -/
structure CAR (ι : Type*) [DecidableEq ι] (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    extends AlgebraicCAR ι V where
  adjoint_compat : ∀ i, creation i = LinearMap.adjoint (annihilation i)

section Occupations

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma ket_apply (S T : Occupation ι) :
    ket S T = if T = S then (1 : ℂ) else 0 := by sorry

lemma coordinates_ket (S T : Occupation ι) :
    coordinates ι (ket S) T = if T = S then (1 : ℂ) else 0 := by sorry

lemma ket_inner (S T : Occupation ι) :
    inner ℂ (ket S) (ket T) = if S = T then (1 : ℂ) else 0 := by sorry

lemma ket_norm (S : Occupation ι) : ‖ket S‖ = 1 := by sorry

lemma ket_ne_zero (S : Occupation ι) : ket S ≠ 0 := by sorry

lemma vacuum_ne_zero : ket (∅ : Occupation ι) ≠ 0 := by sorry

lemma fock_inner (u v : FockSpace ι) :
    inner ℂ u v = ∑ S : Occupation ι, conj (u S) * v S := by sorry

lemma occupation_expansion (v : FockSpace ι) :
    v = ∑ S : Occupation ι, v S • ket S := by sorry

lemma extend_basis_ket (images : Occupation ι → FockSpace ι) (S : Occupation ι) :
    extendBasis images (ket S) = images S := by sorry

lemma end_ext_basis (A B : Module.End ℂ (FockSpace ι))
    (h : ∀ S : Occupation ι, A (ket S) = B (ket S)) : A = B := by sorry

lemma adjoint_of_basis_pairing (A B : Module.End ℂ (FockSpace ι))
    (h : ∀ S T : Occupation ι, inner ℂ (ket S) (A (ket T)) =
      inner ℂ (B (ket S)) (ket T)) : B = LinearMap.adjoint A := by sorry

lemma fock_finrank : Module.finrank ℂ (FockSpace ι) = 2 ^ Fintype.card ι := by sorry

lemma empty_modes_finrank [IsEmpty ι] : Module.finrank ℂ (FockSpace ι) = 1 := by sorry

end Occupations

end Bosonize.A02
