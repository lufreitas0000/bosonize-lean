module

public import Bosonize.Core.CoupledWire.BlochDiracAndGauge
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# `N = 1` QED₃ Mass/Current Duality, Universal Transverse Projector & Conductivity Inversion

Formalizes Mross–Alicea–Motrunich (`arXiv:1510.08455`, Sec. VI & App. 7) on pinned Mathlib4:
- exact nearest-neighbor hopping `D^T` duality `nnHopping_duality_exact`;
- `GaussianInt` mass and current bilinear correspondences (`massBilinear` invariant,
  `currentBilinear` acquires `(-1)^{y+1}`, exact sum correspondence);
- universal Euclidean transverse projector `transProj` over arbitrary `[Fintype ι] [DecidableEq ι]`
  `[CommRing R]` (symmetry, transversality, cleared-denominator idempotence, and
  `trace = (card ι - 1) ‖q‖²`), superseding fixed-`Fin 3` `transProj3D`;
- cleared-denominator irreducible conductivity duality and inverse-product theorems (`σ_J σ_irred = 1`).
-/

@[expose] public section

namespace Bosonize.CoupledWire

open scoped BigOperators
open Matrix

/-! ### 1. `N = 1` QED₃ Nearest-Neighbor Hopping & Bilinear Correspondences -/

/-- Exact nearest-neighbor hopping duality `(D^T Δ_{y,·})_z = -(-1)^y Δ_{y,z}` for `y + 1 < n`. -/
theorem nnHopping_duality_exact (n y z : ℕ) (hy : y + 1 < n) :
    dualityTransposeApply n (fun k => diffLinkEntry y k) z = -paritySign y * diffLinkEntry y z := by
  simp only [dualityTransposeApply]
  have hrew : ∀ k ∈ Finset.range n,
      diffLinkEntry y k * dualityEntry k z =
        (if k = y + 1 then dualityEntry (y + 1) z else 0) +
        (if k = y then -dualityEntry y z else 0) := by
    intro k _; unfold diffLinkEntry
    by_cases h1 : k = y + 1
    · subst h1; simp
    · by_cases h2 : k = y
      · subst h2; simp
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range n) (y + 1), Finset.sum_ite_eq' (Finset.range n) y]
  simp only [Finset.mem_range.mpr hy, Finset.mem_range.mpr (by omega : y < n), ↓reduceIte]
  have hint := interior_delta_duality_exact y z
  linarith

/-- Dual wire bilinear: complex-conjugate on even wires, unchanged on odd wires. -/
def dualBilinear (y : ℕ) (B : GaussianInt) : GaussianInt :=
  if y % 2 = 0 then star B else B

/-- Hermitian mass bilinear `B + B^* = 2 Re(B)`. -/
def massBilinear (B : GaussianInt) : GaussianInt := B + star B

/-- Hermitian current bilinear `i B + (i B)^* = -2 Im(B)`. -/
def currentBilinear (B : GaussianInt) : GaussianInt :=
  (⟨0, 1⟩ : GaussianInt) * B + star ((⟨0, 1⟩ : GaussianInt) * B)

theorem massBilinear_dual_eq (y : ℕ) (B : GaussianInt) :
    massBilinear (dualBilinear y B) = massBilinear B := by
  unfold massBilinear dualBilinear; split_ifs <;> (ext <;> simp)

theorem currentBilinear_dual_eq (y : ℕ) (B : GaussianInt) :
    currentBilinear (dualBilinear y B) = (paritySign (y + 1) : GaussianInt) * currentBilinear B := by
  rw [paritySign_succ]
  unfold currentBilinear dualBilinear paritySign
  split_ifs <;> (ext <;> simp)

theorem qed3_mass_and_current_sum_correspondence (n : ℕ) (m : ℤ) (B : ℕ → GaussianInt) :
    (m * ∑ y ∈ Finset.range n, (massBilinear (dualBilinear y (B y))).re =
      m * ∑ y ∈ Finset.range n, (massBilinear (B y)).re) ∧
    (∑ y ∈ Finset.range n, (currentBilinear (dualBilinear y (B y))).re =
      ∑ y ∈ Finset.range n, paritySign (y + 1) * (currentBilinear (B y)).re) ∧
    (∑ y ∈ Finset.range n, paritySign (y + 1) * (currentBilinear (dualBilinear y (B y))).re =
      ∑ y ∈ Finset.range n, (currentBilinear (B y)).re) := by
  refine ⟨by congr 1; exact Finset.sum_congr rfl (fun y _ => by rw [massBilinear_dual_eq]), ?_, ?_⟩
  · exact Finset.sum_congr rfl (fun y _ => by rw [currentBilinear_dual_eq]; simp)
  · apply Finset.sum_congr rfl; intro y _
    rw [currentBilinear_dual_eq]; simp
    linear_combination (currentBilinear (B y)).re * paritySign_sq (y + 1)

/-! ### 2. Universal Euclidean Transverse Projector & Irreducible Conductivity Duality -/

/-- Squared Euclidean momentum norm `‖q‖² = ∑_μ q_μ²` for any `[Fintype ι]` and `[CommRing R]`. -/
def euclidNormSq {ι R : Type*} [Fintype ι] [CommRing R] (q : ι → R) : R :=
  ∑ μ : ι, q μ ^ 2

/-- Universal cleared-denominator Euclidean transverse projector `P_{μ,ν}(q) = ‖q‖² δ_{μ,ν} - q_μ q_ν`
over arbitrary `[Fintype ι] [DecidableEq ι] [CommRing R]`. -/
def transProj {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (q : ι → R) : Matrix ι ι R :=
  euclidNormSq q • (1 : Matrix ι ι R) - Matrix.vecMulVec q q

theorem transProj_transpose {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (q : ι → R) :
    (transProj q)ᵀ = transProj q := by
  ext μ ν; simp [transProj, Matrix.one_apply, Matrix.vecMulVec_apply, eq_comm, mul_comm]

theorem transProj_mulVec_self {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (q : ι → R) :
    transProj q *ᵥ q = 0 := by
  rw [transProj, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext μ
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.mulVec, dotProduct,
    Matrix.vecMulVec_apply]
  have h : ∑ ν : ι, q μ * q ν * q ν = q μ * euclidNormSq q := by
    rw [euclidNormSq, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun ν _ => by ring)
  rw [h]; ring

theorem transProj_mul_self {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (q : ι → R) :
    transProj q * transProj q = euclidNormSq q • transProj q := by
  ext μ ν
  simp only [transProj, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  have hsum :
      ∑ k : ι,
        (euclidNormSq q * (if μ = k then (1 : R) else 0) - q μ * q k) *
        (euclidNormSq q * (if k = ν then (1 : R) else 0) - q k * q ν) =
      euclidNormSq q ^ 2 * (if μ = ν then (1 : R) else 0) -
        2 * euclidNormSq q * (q μ * q ν) + (q μ * q ν) * euclidNormSq q := by
    have hsplit : ∀ k : ι,
        (euclidNormSq q * (if μ = k then (1 : R) else 0) - q μ * q k) *
        (euclidNormSq q * (if k = ν then (1 : R) else 0) - q k * q ν) =
        (if k = μ then euclidNormSq q ^ 2 * (if μ = ν then (1 : R) else 0) else 0) -
        (if k = μ then euclidNormSq q * (q μ * q ν) else 0) -
        (if k = ν then euclidNormSq q * (q μ * q ν) else 0) +
        (q μ * q ν) * q k ^ 2 := by
      intro k
      by_cases h1 : k = μ <;> by_cases h2 : k = ν
      · subst h1; subst h2; simp; ring
      · subst h1; simp [h2]; ring
      · subst h2; simp [h1, Ne.symm h1]; ring
      · simp [h1, Ne.symm h1, h2]; ring
    rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ μ, Finset.sum_ite_eq' Finset.univ μ,
      Finset.sum_ite_eq' Finset.univ ν, ← Finset.mul_sum]
    simp only [Finset.mem_univ, ↓reduceIte]
    rw [← euclidNormSq]
    ring
  rw [hsum]; ring

theorem transProj_trace {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (q : ι → R) :
    Matrix.trace (transProj q) = ((Fintype.card ι : R) - 1) * euclidNormSq q := by
  rw [transProj, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Matrix.trace_vecMulVec,
    smul_eq_mul, dotProduct]
  have h : ∑ μ : ι, q μ * q μ = euclidNormSq q :=
    Finset.sum_congr rfl (fun μ _ => (sq (q μ)).symm)
  rw [h]; ring

theorem qed3_irred_conductivity_exact (K_jtilde K_J K_jtilde_irred kappa q2 : ℤ)
    (hkappa : kappa ≠ 0) (hq2 : q2 ≠ 0)
    (hKj : K_jtilde = kappa * q2 - kappa ^ 2 * q2 * K_J)
    (hIrred : K_jtilde_irred * (kappa * q2 - K_jtilde) = kappa * q2 * K_jtilde) :
    (K_jtilde_irred + kappa * q2) * K_J = q2 := by
  have hfac : kappa ^ 2 * q2 * ((K_jtilde_irred + kappa * q2) * K_J - q2) = 0 := by
    rw [hKj] at hIrred; linear_combination hIrred
  have hdiff := (mul_eq_zero.mp hfac).resolve_left (mul_ne_zero (pow_ne_zero 2 hkappa) hq2)
  omega

theorem qed3_irred_conductivity_converse {R : Type*} [CommRing R]
    (K_jtilde K_J K_jtilde_irred kappa q2 : R)
    (hKj : K_jtilde = kappa * q2 - kappa ^ 2 * q2 * K_J)
    (hDual : (K_jtilde_irred + kappa * q2) * K_J = q2) :
    K_jtilde_irred * (kappa * q2 - K_jtilde) = kappa * q2 * K_jtilde := by
  rw [hKj]; linear_combination (kappa ^ 2 * q2) * hDual

theorem qed3_conductivity_inverse_product_int (K_J K_jtilde_irred kappa qAbs sigma_J sigma_irred : ℤ)
    (hq : qAbs ≠ 0)
    (hDual : (K_jtilde_irred + kappa * qAbs ^ 2) * K_J = qAbs ^ 2)
    (hKJ : K_J = sigma_J * qAbs)
    (hKirr : K_jtilde_irred + kappa * qAbs ^ 2 = sigma_irred * qAbs) :
    sigma_J * sigma_irred = 1 := by
  rw [hKJ, hKirr] at hDual
  have hfac : qAbs ^ 2 * (sigma_J * sigma_irred - 1) = 0 := by linear_combination hDual
  have hdiff := (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 2 hq)
  omega

theorem qed3_conductivity_inverse_product_cleared
    (K_J K_jtilde_irred kappa qAbs num_J den_J num_irred den_irred : ℤ)
    (hq : qAbs ≠ 0)
    (hDual : (K_jtilde_irred + kappa * qAbs ^ 2) * K_J = qAbs ^ 2)
    (hKJ : den_J * K_J = num_J * qAbs)
    (hKirr : den_irred * (K_jtilde_irred + kappa * qAbs ^ 2) = num_irred * qAbs) :
    num_J * num_irred = den_J * den_irred := by
  have hfac : qAbs ^ 2 * (num_J * num_irred - den_J * den_irred) = 0 := by
    linear_combination (den_J * den_irred) * hDual - (den_J * K_J) * hKirr - (num_irred * qAbs) * hKJ
  have hdiff := (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 2 hq)
  omega

end Bosonize.CoupledWire
