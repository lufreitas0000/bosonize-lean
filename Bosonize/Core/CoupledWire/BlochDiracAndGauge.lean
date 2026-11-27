module

public import Bosonize.Core.CoupledWire.DualityBoundary
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# 2D Coupled-Wire Bloch Dirac Cone, Discrete Symmetries & Dual-Fermion Gauge-Lattice Algebra

Formalizes the Mross–Alicea–Motrunich (`arXiv:1510.08455`) `2×2` Bloch Dirac matrix over
Mathlib4 `GaussianInt` (`ℤ[i]`) and `Matrix (Fin 2) (Fin 2)` together with the finite-`N_y`
dual-fermion gauge-lattice identities:
- Pauli matrices `pauliX`, `pauliY`, `pauliZ`, `timeRevOp` (`T = i σ_y`), `mamTimeRevOpHomog`;
- homogeneous & unit-circle `blochWireMatrix`, `H^2 = (v^2 k_x^2 + m^2) I_2`, single-Dirac-node
  uniqueness at `(0, π)`, dimerized bulk gapping (`|t1| ≠ |t2|`), and 2-node doubled-lattice contrast;
- Hermiticity, chiral `σ_z`, `σ_y H^T σ_y = -H`, `σ_y H^* σ_y = -H`, `σ_x H^* σ_x`, inversion `σ_x`,
  and MAM nonsymmorphic staggered-bond time-reversal covariance;
- finite-`N_y` skew quadratic vanishing, `Δ (D P) = S`, gauge-shift decoupling, `K_MAM = 2 Δ^{-1,T}`
  (`K_MAM P = -(D + P)`, `Δ^T K_MAM a = 2 a` for neutral `a`), and dual kinetic cancellation.
-/

@[expose] public section

namespace Bosonize.CoupledWire

open scoped BigOperators
open Matrix

/-! ### 1. Pauli & Time-Reversal Matrices on Mathlib `Matrix (Fin 2) (Fin 2)` -/

/-- Pauli `σ_x`, `σ_y`, `σ_z` and spinful `T = i σ_y` matrices on `Matrix (Fin 2) (Fin 2)`. -/
def pauliX (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]
def pauliY : Matrix (Fin 2) (Fin 2) GaussianInt := !![0, ⟨0, -1⟩; ⟨0, 1⟩, 0]
def pauliZ (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, -1]
def timeRevOp (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]

/-- Homogeneous and unit-circle nonsymmorphic half-unit-cell time-reversal operators. -/
def mamTimeRevOpHomog (r c s : ℤ) : Matrix (Fin 2) (Fin 2) GaussianInt := !![0, ⟨-c, -s⟩; ⟨r, 0⟩, 0]
def mamTimeRevOp (c s : ℤ) : Matrix (Fin 2) (Fin 2) GaussianInt := mamTimeRevOpHomog 1 c s

theorem pauliX_sq (R : Type*) [CommRing R] : pauliX R * pauliX R = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliZ_sq (R : Type*) [CommRing R] : pauliZ R * pauliZ R = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliY_sq_scale (a : ℤ) :
    ((a : GaussianInt) • pauliY) * pauliY = (a : GaussianInt) • (1 : Matrix (Fin 2) (Fin 2) GaussianInt) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

/-- Kramers antiunitary square `T^2 = -I_2` over arbitrary `[CommRing R]`. -/
theorem timeRevOp_sq (R : Type*) [CommRing R] : timeRevOp R * timeRevOp R = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [timeRevOp, Matrix.mul_apply, Fin.sum_univ_two]

theorem timeRevOp_map_star (a : ℤ) :
    ((a : GaussianInt) • timeRevOp GaussianInt).map star = (a : GaussianInt) • timeRevOp GaussianInt := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [timeRevOp]

/-! ### 2. Coupled-Wire `2×2` Bloch Dirac Matrix & Single-Node Uniqueness -/

/-- Homogeneous `2×2` Bloch coupled-wire Dirac matrix
`H(k_x, c/r, s/r) = v k_x σ_z + (t1 r + t2 c) σ_x + (t2 s) σ_y`. -/
def blochWireMatrixHomog (v kx t1 t2 r c s : ℤ) : Matrix (Fin 2) (Fin 2) GaussianInt :=
  !![⟨v * kx, 0⟩, ⟨t1 * r + t2 * c, -(t2 * s)⟩;
     ⟨t1 * r + t2 * c, t2 * s⟩, ⟨-(v * kx), 0⟩]

/-- Unit-circle `2×2` Bloch coupled-wire Dirac matrix (`r = 1`). -/
def blochWireMatrix (v kx t1 t2 c s : ℤ) : Matrix (Fin 2) (Fin 2) GaussianInt :=
  blochWireMatrixHomog v kx t1 t2 1 c s

/-- Off-diagonal mass-squared term `(t1 r + t2 c)^2 + (t2 s)^2`. -/
def blochOffDiagNormSqHomog (t1 t2 r c s : ℤ) : ℤ :=
  (t1 * r + t2 * c) ^ 2 + (t2 * s) ^ 2

/-- Unit-circle off-diagonal mass-squared term `(t1 + t2 c)^2 + (t2 s)^2`. -/
def blochOffDiagNormSq (t1 t2 c s : ℤ) : ℤ :=
  (t1 + t2 * c) ^ 2 + (t2 * s) ^ 2

/-- Naive 2-node doubled lattice Bloch matrix `v k_x σ_z + t s σ_x`. -/
def doubledLatticeMatrix (v kx t s : ℤ) : Matrix (Fin 2) (Fin 2) GaussianInt :=
  !![⟨v * kx, 0⟩, ⟨t * s, 0⟩; ⟨t * s, 0⟩, ⟨-(v * kx), 0⟩]

theorem blochWireMatrix_eq_homog_one (v kx t1 t2 c s : ℤ) :
    blochWireMatrix v kx t1 t2 c s = blochWireMatrixHomog v kx t1 t2 1 c s := rfl

theorem blochOffDiagNormSqHomog_eq (t1 t2 r c s : ℤ) (hcircle : c ^ 2 + s ^ 2 = r ^ 2) :
    blochOffDiagNormSqHomog t1 t2 r c s =
      (t1 ^ 2 + t2 ^ 2) * r ^ 2 + 2 * t1 * t2 * r * c := by
  unfold blochOffDiagNormSqHomog; linear_combination t2 ^ 2 * hcircle

theorem blochOffDiagNormSq_unit (t1 t2 c s : ℤ) (hcircle : c ^ 2 + s ^ 2 = 1) :
    blochOffDiagNormSq t1 t2 c s = t1 ^ 2 + t2 ^ 2 + 2 * t1 * t2 * c := by
  have h := blochOffDiagNormSqHomog_eq t1 t2 1 c s (by simpa using hcircle)
  simpa [blochOffDiagNormSq, blochOffDiagNormSqHomog] using h

/-- Exact Bloch Hamiltonian square `H^2 = (v^2 k_x^2 + m^2) I_2` (homogeneous form). -/
theorem blochWireMatrixHomog_sq (v kx t1 t2 r c s : ℤ) :
    blochWireMatrixHomog v kx t1 t2 r c s * blochWireMatrixHomog v kx t1 t2 r c s =
      ((v ^ 2 * kx ^ 2 + blochOffDiagNormSqHomog t1 t2 r c s : ℤ) : GaussianInt) •
        (1 : Matrix (Fin 2) (Fin 2) GaussianInt) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [blochWireMatrixHomog, blochOffDiagNormSqHomog, Matrix.mul_apply, Fin.sum_univ_two,
      -Int.cast_add, -Int.cast_mul, -Int.cast_pow, -Int.cast_sub, -Int.cast_neg] <;> ring

theorem blochWireMatrix_sq_unit (v kx t1 t2 c s : ℤ) (hcircle : c ^ 2 + s ^ 2 = 1) :
    blochWireMatrix v kx t1 t2 c s * blochWireMatrix v kx t1 t2 c s =
      ((v ^ 2 * kx ^ 2 + (t1 ^ 2 + t2 ^ 2 + 2 * t1 * t2 * c) : ℤ) : GaussianInt) •
        (1 : Matrix (Fin 2) (Fin 2) GaussianInt) := by
  rw [blochWireMatrix_eq_homog_one, blochWireMatrixHomog_sq]
  have hnorm : blochOffDiagNormSqHomog t1 t2 1 c s = t1 ^ 2 + t2 ^ 2 + 2 * t1 * t2 * c := by
    simpa [blochOffDiagNormSqHomog, blochOffDiagNormSq] using blochOffDiagNormSq_unit t1 t2 c s hcircle
  rw [hnorm]

private theorem sum_three_sq_eq_zero {x y z : ℤ} (h : x ^ 2 + y ^ 2 + z ^ 2 = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have hx : 0 ≤ x ^ 2 := sq_nonneg x
  have hy : 0 ≤ y ^ 2 := sq_nonneg y
  have hz : 0 ≤ z ^ 2 := sq_nonneg z
  exact ⟨sq_eq_zero_iff.mp (by linarith), sq_eq_zero_iff.mp (by linarith),
    sq_eq_zero_iff.mp (by linarith)⟩

/-- Homogeneous single-Dirac-node uniqueness on rational `S^1` (`c^2 + s^2 = r^2`, `r ≠ 0`):
for `v ≠ 0, t1 = t2 ≠ 0`, `H^2 = 0 ↔ k_x = 0 ∧ c = -r ∧ s = 0`. -/
theorem blochWireHomog_single_node_uniqueness (v kx t1 t2 r c s : ℤ)
    (hv : v ≠ 0) (ht : t1 ≠ 0) (heq : t1 = t2) (_hr : r ≠ 0) (_hcircle : c ^ 2 + s ^ 2 = r ^ 2) :
    blochWireMatrixHomog v kx t1 t2 r c s * blochWireMatrixHomog v kx t1 t2 r c s = 0 ↔
      (kx = 0 ∧ c = -r ∧ s = 0) := by
  subst heq
  constructor
  · intro hzero
    rw [blochWireMatrixHomog_sq] at hzero
    have ha00 : (v ^ 2 * kx ^ 2 + blochOffDiagNormSqHomog t1 t1 r c s : ℤ) = 0 := by
      have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) GaussianInt => (M 0 0).re) hzero
      simpa [-Int.cast_add, -Int.cast_mul, -Int.cast_pow] using h
    have hsum : (v * kx) ^ 2 + (t1 * (r + c)) ^ 2 + (t1 * s) ^ 2 = 0 := by
      unfold blochOffDiagNormSqHomog at ha00; linarith
    obtain ⟨h1, h2, h3⟩ := sum_three_sq_eq_zero hsum
    exact ⟨(mul_eq_zero.mp h1).resolve_left hv,
      by have := (mul_eq_zero.mp h2).resolve_left ht; linarith,
      (mul_eq_zero.mp h3).resolve_left ht⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rw [blochWireMatrixHomog_sq]
    have hzero : v ^ 2 * 0 ^ 2 + blochOffDiagNormSqHomog t1 t1 r (-r) 0 = 0 := by
      unfold blochOffDiagNormSqHomog; ring
    rw [hzero]; simp

theorem blochWire_single_node_uniqueness (v kx t1 t2 c s : ℤ)
    (hv : v ≠ 0) (ht : t1 ≠ 0) (heq : t1 = t2) (hcircle : c ^ 2 + s ^ 2 = 1) :
    blochWireMatrix v kx t1 t2 c s * blochWireMatrix v kx t1 t2 c s = 0 ↔
      (kx = 0 ∧ c = -1 ∧ s = 0) := by
  simpa [blochWireMatrix] using
    blochWireHomog_single_node_uniqueness v kx t1 t2 1 c s hv ht heq one_ne_zero (by simpa using hcircle)

/-- Homogeneous dimerized bulk gapping: whenever `t1^2 ≠ t2^2` on `c^2 + s^2 = r^2` (`r ≠ 0`),
`H_homog^2 ≠ 0`. -/
theorem blochWireHomog_dimerized_gapped (v kx t1 t2 r c s : ℤ)
    (hr : r ≠ 0) (hgap : t1 ^ 2 ≠ t2 ^ 2) (hcircle : c ^ 2 + s ^ 2 = r ^ 2) :
    blochWireMatrixHomog v kx t1 t2 r c s * blochWireMatrixHomog v kx t1 t2 r c s ≠ 0 := by
  intro hzero
  rw [blochWireMatrixHomog_sq] at hzero
  have ha00 : (v ^ 2 * kx ^ 2 + blochOffDiagNormSqHomog t1 t2 r c s : ℤ) = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) GaussianInt => (M 0 0).re) hzero
    simpa [-Int.cast_add, -Int.cast_mul, -Int.cast_pow] using h
  have hsum : (v * kx) ^ 2 + (t1 * r + t2 * c) ^ 2 + (t2 * s) ^ 2 = 0 := by
    unfold blochOffDiagNormSqHomog at ha00; linarith
  obtain ⟨_, h2, h3⟩ := sum_three_sq_eq_zero hsum
  by_cases hs : s = 0
  · have hcsq : c ^ 2 = r ^ 2 := by rw [hs] at hcircle; linarith
    have hcases : c = r ∨ c = -r := sq_eq_sq_iff_eq_or_eq_neg.mp hcsq
    have hmul : (t1 ^ 2 - t2 ^ 2) * r ^ 2 = 0 := by
      rcases hcases with hcr | hcr
      · rw [hcr] at h2; linear_combination (t1 - t2) * r * h2
      · rw [hcr] at h2; linear_combination (t1 + t2) * r * h2
    exact hgap (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right (pow_ne_zero 2 hr)))
  · have ht2 : t2 = 0 := (mul_eq_zero.mp h3).resolve_right hs
    subst ht2; simp only [zero_mul, add_zero] at h2
    have ht1 : t1 = 0 := (mul_eq_zero.mp h2).resolve_right hr
    subst ht1; exact hgap rfl

theorem blochWire_dimerized_gapped (v kx t1 t2 c s : ℤ)
    (hgap : t1 ^ 2 ≠ t2 ^ 2) (hcircle : c ^ 2 + s ^ 2 = 1) :
    blochWireMatrix v kx t1 t2 c s * blochWireMatrix v kx t1 t2 c s ≠ 0 :=
  blochWireHomog_dimerized_gapped v kx t1 t2 1 c s one_ne_zero hgap (by simpa using hcircle)

theorem doubledLatticeMatrix_sq (v kx t s : ℤ) :
    doubledLatticeMatrix v kx t s * doubledLatticeMatrix v kx t s =
      ((v ^ 2 * kx ^ 2 + (t * s) ^ 2 : ℤ) : GaussianInt) •
        (1 : Matrix (Fin 2) (Fin 2) GaussianInt) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [doubledLatticeMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      -Int.cast_add, -Int.cast_mul, -Int.cast_pow] <;> ring

theorem doubledLatticeHomog_two_nodes (v kx t r c s : ℤ)
    (hv : v ≠ 0) (ht : t ≠ 0) (_hr : r ≠ 0) (hcircle : c ^ 2 + s ^ 2 = r ^ 2) :
    doubledLatticeMatrix v kx t s * doubledLatticeMatrix v kx t s = 0 ↔
      (kx = 0 ∧ s = 0 ∧ c ^ 2 = r ^ 2) := by
  constructor
  · intro hzero
    rw [doubledLatticeMatrix_sq] at hzero
    have ha00 : v ^ 2 * kx ^ 2 + (t * s) ^ 2 = 0 := by
      have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) GaussianInt => (M 0 0).re) hzero
      simpa [-Int.cast_add, -Int.cast_mul, -Int.cast_pow] using h
    obtain ⟨h1, h2, _⟩ := sum_three_sq_eq_zero (x := v * kx) (y := t * s) (z := 0) (by linarith)
    have hkx := (mul_eq_zero.mp h1).resolve_left hv
    have hs := (mul_eq_zero.mp h2).resolve_left ht
    exact ⟨hkx, hs, by rw [hs] at hcircle; linarith⟩
  · rintro ⟨rfl, rfl, _⟩; rw [doubledLatticeMatrix_sq]; simp

theorem doubledLatticeHomog_distinct_zeros (v t r : ℤ) (hr : r ≠ 0) :
    doubledLatticeMatrix v 0 t 0 * doubledLatticeMatrix v 0 t 0 = 0 ∧
    (r ^ 2 + (0 : ℤ) ^ 2 = r ^ 2) ∧ ((-r) ^ 2 + (0 : ℤ) ^ 2 = r ^ 2) ∧ (r ≠ -r) := by
  refine ⟨by rw [doubledLatticeMatrix_sq]; simp, by ring, by ring, by omega⟩

theorem doubledLattice_two_nodes (v kx t c s : ℤ)
    (hv : v ≠ 0) (ht : t ≠ 0) (hcircle : c ^ 2 + s ^ 2 = 1) :
    doubledLatticeMatrix v kx t s * doubledLatticeMatrix v kx t s = 0 ↔
      (kx = 0 ∧ s = 0 ∧ c ^ 2 = 1) := by
  simpa using doubledLatticeHomog_two_nodes v kx t 1 c s hv ht one_ne_zero (by simpa using hcircle)

/-! ### 3. Discrete Symmetries on `2×2` Bloch Space -/

theorem blochWireMatrix_hermitian (v kx t1 t2 c s : ℤ) :
    (blochWireMatrix v kx t1 t2 c s)ᴴ = blochWireMatrix v kx t1 t2 c s := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [blochWireMatrix, blochWireMatrixHomog, Matrix.conjTranspose_apply]

theorem blochWireMatrix_chiral_sz (v kx t1 t2 c s : ℤ) :
    pauliZ GaussianInt * blochWireMatrix v kx t1 t2 c s * pauliZ GaussianInt =
      -blochWireMatrix v (-kx) t1 t2 c s := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliZ, blochWireMatrix, blochWireMatrixHomog, Matrix.mul_apply, Fin.sum_univ_two]

theorem blochWireMatrix_sigmaY_transpose (v kx t1 t2 c s : ℤ) :
    pauliY * (blochWireMatrix v kx t1 t2 c s)ᵀ * pauliY =
      -blochWireMatrix v kx t1 t2 c s := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliY, blochWireMatrix, blochWireMatrixHomog, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two]

theorem blochWireMatrix_sigmaY_conj (v kx t1 t2 c s : ℤ) :
    pauliY * (blochWireMatrix v kx t1 t2 c s).map star * pauliY =
      -blochWireMatrix v kx t1 t2 c s := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliY, blochWireMatrix, blochWireMatrixHomog, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two]

theorem blochWireMatrix_sigmaX_conj (v kx t1 t2 c s : ℤ) :
    pauliX GaussianInt * (blochWireMatrix v kx t1 t2 c s).map star * pauliX GaussianInt =
      blochWireMatrix v (-kx) t1 t2 c s := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliX, blochWireMatrix, blochWireMatrixHomog, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two]

theorem blochWireMatrix_inversion (v kx t1 t2 c s : ℤ) :
    pauliX GaussianInt * blochWireMatrix v kx t1 t2 c s * pauliX GaussianInt =
      blochWireMatrix v (-kx) t1 t2 c (-s) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliX, blochWireMatrix, blochWireMatrixHomog, Matrix.mul_apply, Fin.sum_univ_two]

/-- Homogeneous MAM nonsymmorphic staggered-bond time-reversal covariance across ALL rational
unit-circle points `c^2 + s^2 = r^2` (`t1 = -w, t2 = w`). -/
theorem blochWireMatrixHomog_mam_time_reversal (v kx w r c s : ℤ) (hcircle : c ^ 2 + s ^ 2 = r ^ 2) :
    mamTimeRevOpHomog r c s * (blochWireMatrixHomog v kx (-w) w r c s).map star *
        (mamTimeRevOpHomog r c s)ᴴ =
      ((r ^ 2 : ℤ) : GaussianInt) • blochWireMatrixHomog v (-kx) (-w) w r c (-s) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [mamTimeRevOpHomog, blochWireMatrixHomog, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, -Int.cast_pow] <;>
    first | ring1 | linear_combination -(v * kx) * hcircle | linear_combination -(w * r) * hcircle

theorem mamTimeRevOpHomog_bloch_sq (r c s : ℤ) :
    mamTimeRevOpHomog r c s * (mamTimeRevOpHomog r c (-s)).map star =
      (⟨-(r * c), -(r * s)⟩ : GaussianInt) • (1 : Matrix (Fin 2) (Fin 2) GaussianInt) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [mamTimeRevOpHomog, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem mamTimeRevOp_bloch_sq (c s : ℤ) :
    mamTimeRevOp c s * (mamTimeRevOp c (-s)).map star =
      (⟨-c, -s⟩ : GaussianInt) • (1 : Matrix (Fin 2) (Fin 2) GaussianInt) := by
  simpa [mamTimeRevOp] using mamTimeRevOpHomog_bloch_sq 1 c s

theorem blochWireMatrix_mam_time_reversal (v kx w c s : ℤ) (hcircle : c ^ 2 + s ^ 2 = 1) :
    mamTimeRevOp c s * (blochWireMatrix v kx (-w) w c s).map star * (mamTimeRevOp c s)ᴴ =
      blochWireMatrix v (-kx) (-w) w c (-s) := by
  have h := blochWireMatrixHomog_mam_time_reversal v kx w 1 c s (by simpa using hcircle)
  simpa [mamTimeRevOp, blochWireMatrix] using h

/-! ### 4. Finite-`N_y` MAM Dual-Fermion Gauge-Lattice Identities -/

/-- Every quadratic form of a skew-symmetric matrix `M y z = -M z y` vanishes identically. -/
theorem quadratic_skew_zero (n : ℕ) (M : ℕ → ℕ → ℤ) (hskew : ∀ y z, M y z = -M z y) (u : ℕ → ℤ) :
    ∑ y ∈ Finset.range n, u y * (∑ z ∈ Finset.range n, M y z * u z) = 0 := by
  have hsum :
      ∑ y ∈ Finset.range n, u y * (∑ z ∈ Finset.range n, M y z * u z) =
        -(∑ y ∈ Finset.range n, u y * (∑ z ∈ Finset.range n, M y z * u z)) := by
    calc
      ∑ y ∈ Finset.range n, u y * (∑ z ∈ Finset.range n, M y z * u z)
          = ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n, u y * (M y z * u z) := by
            simp_rw [Finset.mul_sum]
      _ = ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n, -(u z * (M z y * u y)) := by
            apply Finset.sum_congr rfl; intro y _; apply Finset.sum_congr rfl; intro z _
            rw [hskew y z]; ring
      _ = -(∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n, u z * (M z y * u y)) := by
            simp_rw [Finset.sum_neg_distrib]
      _ = -(∑ z ∈ Finset.range n, ∑ y ∈ Finset.range n, u z * (M z y * u y)) := by
            rw [Finset.sum_comm]
      _ = -(∑ y ∈ Finset.range n, u y * (∑ z ∈ Finset.range n, M y z * u z)) := by
            simp_rw [← Finset.mul_sum]
  omega

/-- Exact interior link-row identity `(Δ (D P))_{y,z} = S_{y,z}` (MAM App. 3 Eq. (60)). -/
theorem interior_delta_dp_eq_s (y z : ℕ) :
    (dualityEntry (y + 1) z - dualityEntry y z) * paritySign z = shiftLinkEntry y z := by
  rw [interior_delta_duality_exact y z]
  have h1 := pspp_eq_neg_delta y z
  have hpy := paritySign_sq y
  have hpz := paritySign_sq z
  linear_combination -(paritySign y * paritySign z) * h1 +
    (shiftLinkEntry y z * paritySign z ^ 2) * hpy + shiftLinkEntry y z * hpz

/-- Exact finite-`N_y` MAM vector-potential decoupling identity (MAM App. 3 Eq. (60)). -/
theorem interior_gauge_shift_exact (n y : ℕ) (v : ℤ) (a0 a1 : ℕ → ℤ) :
    (v * (∑ z ∈ Finset.range n, dualityEntry (y + 1) z * paritySign z * a1 z) -
       ∑ z ∈ Finset.range n, dualityEntry (y + 1) z * a0 z) -
    (v * (∑ z ∈ Finset.range n, dualityEntry y z * paritySign z * a1 z) -
       ∑ z ∈ Finset.range n, dualityEntry y z * a0 z) =
      v * (∑ z ∈ Finset.range n, shiftLinkEntry y z * a1 z) +
        paritySign y * (∑ z ∈ Finset.range n, diffLinkEntry y z * a0 z) := by
  have ha1 :
      (∑ z ∈ Finset.range n, dualityEntry (y + 1) z * paritySign z * a1 z) -
      (∑ z ∈ Finset.range n, dualityEntry y z * paritySign z * a1 z) =
        ∑ z ∈ Finset.range n, shiftLinkEntry y z * a1 z := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro z _
    linear_combination a1 z * interior_delta_dp_eq_s y z
  have ha0 :
      (∑ z ∈ Finset.range n, dualityEntry (y + 1) z * a0 z) -
      (∑ z ∈ Finset.range n, dualityEntry y z * a0 z) =
        -paritySign y * (∑ z ∈ Finset.range n, diffLinkEntry y z * a0 z) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro z _
    linear_combination a0 z * interior_delta_duality_exact y z
  linear_combination v * ha1 - ha0

/-- Doubled inverse-transpose kernel `(2 Δ^{-1,T})_{y,z} = sgn(z - y - 0^+)`. -/
def dualInvTransEntry (y z : ℕ) : ℤ :=
  if y < z then 1 else -1

/-- Exact matrix identity `K_MAM P = -(D + P)` entrywise for all `y, z : ℕ`. -/
theorem dualInvTrans_mul_parity (y z : ℕ) :
    dualInvTransEntry y z * paritySign z =
      -(dualityEntry y z + (if y = z then paritySign y else 0)) := by
  unfold dualInvTransEntry dualityEntry skewSignEntry
  by_cases hyz : y = z
  · subst hyz; simp
  · by_cases hlt : y < z
    · simp [hyz, hlt, show ¬ (z < y) by omega]
    · simp [hyz, hlt, show z < y by omega]

/-- Exact finite-`N_y` matrix product `(Δ_link^T K_MAM)_{i,j}` (`n ≥ 2`, `i, j < n`). -/
theorem deltaT_dualInvTrans_entry (n i j : ℕ) (hn : 2 ≤ n) (hi : i < n) (hj : j < n) :
    ∑ y ∈ Finset.range (n - 1), diffLinkEntry y i * dualInvTransEntry y j =
      (if i = j then 2 else 0) - (if i = 0 ∨ i + 1 = n then 1 else 0) := by
  have hrew : ∀ y ∈ Finset.range (n - 1),
      diffLinkEntry y i * dualInvTransEntry y j =
        (if y = i - 1 then (if 0 < i then dualInvTransEntry (i - 1) j else 0) else 0) +
        (if y = i then -dualInvTransEntry i j else 0) := by
    intro y _; unfold diffLinkEntry
    by_cases h1 : y + 1 = i
    · have hy_eq : y = i - 1 := by omega
      subst hy_eq; simp [show 0 < i by omega, show ¬ (i - 1 = i) by omega, h1]
    · by_cases h2 : y = i
      · subst h2
        by_cases hy0 : y = 0
        · subst hy0; simp
        · simp [show y ≠ y - 1 by omega]
      · by_cases hi0 : i = 0
        · subst hi0; simp [h2]
        · simp [h1, h2, show y ≠ i - 1 by omega]
  rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range (n - 1)) (i - 1),
    Finset.sum_ite_eq' (Finset.range (n - 1)) i]
  simp only [Finset.mem_range, dualInvTransEntry]
  split_ifs <;> omega

/-- Exact inverse-transpose identity `(Δ_link^T K_MAM) a = 2 a` for every neutral vector `a`. -/
theorem deltaT_dualInvTrans_zero_sum_eq_two_id (n i : ℕ) (hn : 2 ≤ n) (hi : i < n)
    (a : ℕ → ℤ) (hsum : ∑ j ∈ Finset.range n, a j = 0) :
    ∑ y ∈ Finset.range (n - 1), diffLinkEntry y i * (∑ j ∈ Finset.range n, dualInvTransEntry y j * a j) =
      2 * a i := by
  simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
  have hinner : ∀ j ∈ Finset.range n,
      ∑ y ∈ Finset.range (n - 1), diffLinkEntry y i * (dualInvTransEntry y j * a j) =
        (if j = i then 2 * a i else 0) - (if i = 0 ∨ i + 1 = n then 1 else 0) * a j := by
    intro j hj
    have hassoc : ∀ y ∈ Finset.range (n - 1),
        diffLinkEntry y i * (dualInvTransEntry y j * a j) =
          (diffLinkEntry y i * dualInvTransEntry y j) * a j := fun y _ => (mul_assoc _ _ _).symm
    rw [Finset.sum_congr rfl hassoc, ← Finset.sum_mul,
      deltaT_dualInvTrans_entry n i j hn hi (Finset.mem_range.mp hj)]
    by_cases hji : j = i
    · subst hji; split_ifs <;> ring
    · simp [hji, Ne.symm hji]
  rw [Finset.sum_congr rfl hinner, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' (Finset.range n) i, ← Finset.mul_sum, hsum, mul_zero, sub_zero]
  simp [Finset.mem_range.mpr hi]

/-- Exact finite-`N_y` dual kinetic cancellation identity (MAM Eqs. (38)–(39)):
`∑_y (D u)_y^2 + ∑_y u_y^2 = ∑_y (K_MAM P u)_y^2` identically for ALL `n` and ALL `u`. -/
theorem dual_kinetic_cancellation_exact (n : ℕ) (u : ℕ → ℤ) :
    ∑ y ∈ Finset.range n,
      ((∑ z ∈ Finset.range n, dualityEntry y z * u z) ^ 2 + u y ^ 2 -
        (∑ z ∈ Finset.range n, dualInvTransEntry y z * paritySign z * u z) ^ 2) = 0 := by
  have hkpu_eq : ∀ y ∈ Finset.range n,
      ∑ z ∈ Finset.range n, dualInvTransEntry y z * paritySign z * u z =
        -((∑ z ∈ Finset.range n, dualityEntry y z * u z) + paritySign y * u y) := by
    intro y hy
    have hrew : ∀ z ∈ Finset.range n,
        dualInvTransEntry y z * paritySign z * u z =
          -(dualityEntry y z * u z + (if z = y then paritySign y * u y else 0)) := by
      intro z _; rw [dualInvTrans_mul_parity y z]
      by_cases hzy : z = y
      · subst hzy; simp; ring
      · simp [hzy, Ne.symm hzy]
    rw [Finset.sum_congr rfl hrew, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' (Finset.range n) y]
    simp [Finset.mem_range.mp hy]
  have hpoint : ∀ y ∈ Finset.range n,
      (∑ z ∈ Finset.range n, dualityEntry y z * u z) ^ 2 + u y ^ 2 -
        (∑ z ∈ Finset.range n, dualInvTransEntry y z * paritySign z * u z) ^ 2 =
        -(2 * (u y * (∑ z ∈ Finset.range n, (paritySign y * dualityEntry y z) * u z))) := by
    intro y hy; rw [hkpu_eq y hy]
    have hpull : ∑ z ∈ Finset.range n, (paritySign y * dualityEntry y z) * u z =
        paritySign y * ∑ z ∈ Finset.range n, dualityEntry y z * u z := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun z _ => mul_assoc _ _ _)
    rw [hpull]; linear_combination -(u y ^ 2) * paritySign_sq y
  rw [Finset.sum_congr rfl hpoint, Finset.sum_neg_distrib, ← Finset.mul_sum,
    quadratic_skew_zero n (fun y z => paritySign y * dualityEntry y z) parityMulDuality_skew u,
    mul_zero, neg_zero]

end Bosonize.CoupledWire
