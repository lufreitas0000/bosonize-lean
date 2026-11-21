import BosonizeStubs.Ch21BudgetAndSWBridge
import BosonizeStubs.Ch21AnalyticSWCore

/-!
# Chapter 21 Analytic Schrieffer-Wolff Remainder: Explicit Two-Level Witness and Umklapp Instantiation

Constructive Phase B formalization instantiating the abstract finite-dimensional analytic
Schrieffer-Wolff Taylor remainder from `BosonizeStubs.Ch21AnalyticSWCore`
(`prop:ch21-sw-analytic-remainder`, `eq:ch21-rem-definition`, `eq:ch21-sw-exact-plus-remainder`,
`eq:ch21-sw-integral-remainder`, `eq:ch21-sw-norm-bound`) onto:

1. **Explicit `2×2` Analytic Schrieffer-Wolff Witness (`ex:ch21-sw-two-level`):**
   On frozen Core `A10.swCounterH0_2x2`, `A10.swCounterV_2x2`, `A10.swCounterS1_2x2`,
   `A10.swCounterP_2x2` (in `Matrix.Norms.L2Operator`):
   - `S₁² = -I`, `S₁ᴴ = -S₁`, and closed trigonometric exponential
     `exp(t S₁) = !![cos t, -sin t; sin t, cos t]`;
   - exact rotated compressed entry `(P H̃(t) P)_{00} = sin² t - t sin(2t)`
     (`eq:ch21-sw-2x2-rotated`) and off-diagonal entry `(H̃(t))_{01} = t cos(2t) - (1/2) sin(2t)`
     (`eq:ch21-sw-2x2-off`);
   - exact eigenvalues `E_±(t) = (1 ± √(1 + 4 t²)) / 2` with globally nonzero eigenvectors for all
     `t : ℝ`, and exact discrepancy at `t = 2/3`: `E_-(2/3) = -1/3 ≠ -4/9 = (H_eff^{[2]}(2/3))_{00}`
     (`eq:ch21-sw-2x2-eigvals`);
   - concrete remainder bound `‖P * R₃(t) * P‖ ≤ ‖R₃(t)‖ ≤ (8 / 3) * |t|³`.

2. **Concrete `Ch21 → A10` Spinful Umklapp Block Analytic Remainder Bounds:**
   - Bridges `A10.bchSecondOrderPolynomial` and `A10.swEffectiveSecondOrder` on `A05.Operators`
     isometrically via `LinearMap.toContinuousLinearMap` into bounded operators
     `A05.FockSpace SpinBranch h →L[ℂ] A05.FockSpace SpinBranch h`;
   - proves exact iterated commutators `ad_{S₁}^3(H₀) = (4 s²) • V`, `ad_{S₁}^2(V) = (-4 s²) • V`
     and exact Hilbert operator norm `‖V‖ = |g_U| / (4 h²)`;
   - instantiates `prop:ch21-sw-analytic-remainder` directly on `umklappBlock_a10_bch_bridge`,
     obtaining `‖P * R₃(t) * P‖ ≤ ‖R₃(t)‖ ≤ |t|³ * |g_U|³ / (96 * h⁸)` for every `0 < h`
     (`|t|³ * |g_U|³ / 24576` at `h = 2`).
-/

namespace Bosonize.Ch21

open scoped BigOperators ComplexConjugate

/-! ## 2. Explicit `2×2` Analytic Schrieffer-Wolff Witness (`ex:ch21-sw-two-level`) -/

section TwoLevelWitness

open scoped Matrix.Norms.L2Operator

/-- Lower exact eigenvalue `E_-(t) = (1 - √(1 + 4 t²)) / 2` of `H₀ + t V`
(`eq:ch21-sw-2x2-eigvals`). -/
noncomputable def swCounterEigvalMinus (t : ℝ) : ℝ :=
  (1 - Real.sqrt (1 + 4 * t ^ 2)) / 2

/-- Upper exact eigenvalue `E_+(t) = (1 + √(1 + 4 t²)) / 2` of `H₀ + t V`
(`eq:ch21-sw-2x2-eigvals`). -/
noncomputable def swCounterEigvalPlus (t : ℝ) : ℝ :=
  (1 + Real.sqrt (1 + 4 * t ^ 2)) / 2

/-- Globally nonzero lower eigenvector `v_-(t) = [-(1 + √(1 + 4 t²)), 2 t]` for `E_-(t)`. -/
noncomputable def swCounterEigvecMinus (t : ℝ) : Fin 2 → ℂ :=
  ![(-(1 + Real.sqrt (1 + 4 * t ^ 2)) : ℝ), (2 * t : ℝ)]

/-- Globally nonzero upper eigenvector `v_+(t) = [2 t, 1 + √(1 + 4 t²)]` for `E_+(t)`. -/
noncomputable def swCounterEigvecPlus (t : ℝ) : Fin 2 → ℂ :=
  ![(2 * t : ℝ), (1 + Real.sqrt (1 + 4 * t ^ 2) : ℝ)]

lemma swCounterS1_2x2_sq :
    A10.swCounterS1_2x2 * A10.swCounterS1_2x2 = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, A10.swCounterS1_2x2]

lemma swCounterS1_2x2_skew :
    star A10.swCounterS1_2x2 = -A10.swCounterS1_2x2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.star_eq_conjTranspose, A10.swCounterS1_2x2]

lemma swCounterP_2x2_ortho :
    A10.swCounterP_2x2 * A10.swCounterP_2x2 = A10.swCounterP_2x2 ∧
    star A10.swCounterP_2x2 = A10.swCounterP_2x2 := by
  constructor <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, A10.swCounterP_2x2])

/-- Closed trigonometric exponential `exp(t S₁) = !![cos t, -sin t; sin t, cos t]` for
`ex:ch21-sw-two-level`. -/
theorem swCounter_2x2_exp_eq (t : ℝ) :
    NormedSpace.exp (t • A10.swCounterS1_2x2) =
      !![(Real.cos t : ℂ), -(Real.sin t : ℂ);
         (Real.sin t : ℂ), (Real.cos t : ℂ)] := by
  rw [exp_smul_of_sq_eq_neg_one swCounterS1_2x2_sq t]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A10.swCounterS1_2x2, Complex.real_smul]

/-- Closed trigonometric inverse exponential `exp(-t S₁) = !![cos t, sin t; -sin t, cos t]`. -/
theorem swCounter_2x2_exp_neg_eq (t : ℝ) :
    NormedSpace.exp ((-t) • A10.swCounterS1_2x2) =
      !![(Real.cos t : ℂ), (Real.sin t : ℂ);
         -(Real.sin t : ℂ), (Real.cos t : ℂ)] := by
  rw [swCounter_2x2_exp_eq (-t)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Real.cos_neg, Real.sin_neg]

/-- Equations `eq:ch21-sw-2x2-rotated`, `eq:ch21-sw-2x2-off`, and `eq:ch21-sw-2x2-effective`:
exact rotated compressed entry `(P H̃(t) P)_{00} = sin² t - t sin(2t)`, off-diagonal entry
`(H̃(t))_{01} = t cos(2t) - (1/2) sin(2t)`, and second-order effective entry
`(H_eff^{[2]}(t))_{00} = -t²`. -/
theorem swCounter_2x2_rotated_entries (t : ℝ) :
    (A10.swCounterP_2x2 *
      swRotatedHam A10.swCounterH0_2x2 A10.swCounterV_2x2 A10.swCounterS1_2x2 t *
      A10.swCounterP_2x2) 0 0 =
        ((Real.sin t ^ 2 - t * Real.sin (2 * t) : ℝ) : ℂ) ∧
    (swRotatedHam A10.swCounterH0_2x2 A10.swCounterV_2x2 A10.swCounterS1_2x2 t) 0 1 =
        ((t * Real.cos (2 * t) - (1 / 2 : ℝ) * Real.sin (2 * t) : ℝ) : ℂ) ∧
    (swEffPoly2 A10.swCounterP_2x2 A10.swCounterH0_2x2 A10.swCounterV_2x2 A10.swCounterS1_2x2 t) 0 0 =
        -((t ^ 2 : ℝ) : ℂ) := by
  have hrot :
      swRotatedHam A10.swCounterH0_2x2 A10.swCounterV_2x2 A10.swCounterS1_2x2 t =
        !![(Real.cos t : ℂ), -(Real.sin t : ℂ); (Real.sin t : ℂ), (Real.cos t : ℂ)] *
          (A10.swCounterH0_2x2 + t • A10.swCounterV_2x2) *
        !![(Real.cos t : ℂ), (Real.sin t : ℂ); -(Real.sin t : ℂ), (Real.cos t : ℂ)] := by
    unfold swRotatedHam swAdjointFlow
    rw [swCounter_2x2_exp_eq t, swCounter_2x2_exp_neg_eq t]
  have hsin2 : Real.sin (2 * t) = 2 * Real.sin t * Real.cos t := Real.sin_two_mul t
  have hcos2 : Real.cos (2 * t) = Real.cos t ^ 2 - Real.sin t ^ 2 := Real.cos_two_mul' t
  refine ⟨?_, ?_, ?_⟩
  · rw [hrot]
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Fin.sum_univ_two,
      A10.swCounterP_2x2, A10.swCounterH0_2x2, A10.swCounterV_2x2, Complex.real_smul,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      ↓reduceIte, Fin.isValue, ne_eq, zero_ne_one, one_ne_zero,
      not_false_eq_true, not_true_eq_false, and_self, and_false, false_and,
      zero_mul, mul_zero, add_zero, zero_add, mul_one, one_mul]
    rw [hsin2]
    push_cast
    ring
  · rw [hrot]
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Fin.sum_univ_two,
      A10.swCounterH0_2x2, A10.swCounterV_2x2, Complex.real_smul,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      ↓reduceIte, Fin.isValue, ne_eq, zero_ne_one, one_ne_zero,
      not_false_eq_true, not_true_eq_false, and_self, and_false, false_and,
      mul_zero, add_zero, zero_add, mul_one]
    rw [hsin2, hcos2]
    push_cast
    ring
  · simp only [swEffPoly2, adOp, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.mul_apply, Fin.sum_univ_two, A10.swCounterP_2x2, A10.swCounterH0_2x2,
      A10.swCounterV_2x2, A10.swCounterS1_2x2, Complex.real_smul]
    norm_num

/-- Equation `eq:ch21-sw-2x2-eigvals`: for every `t : ℝ`, `E_±(t) = (1 ± √(1 + 4 t²)) / 2` are
exact eigenvalues of `H₀ + t V` with globally nonzero eigenvectors `v_±(t)`. -/
theorem swCounter_2x2_exact_eigenvalues (t : ℝ) :
    swCounterEigvecMinus t ≠ 0 ∧
    (A10.swCounterH0_2x2 + t • A10.swCounterV_2x2).mulVec (swCounterEigvecMinus t) =
      (swCounterEigvalMinus t : ℂ) • swCounterEigvecMinus t ∧
    swCounterEigvecPlus t ≠ 0 ∧
    (A10.swCounterH0_2x2 + t • A10.swCounterV_2x2).mulVec (swCounterEigvecPlus t) =
      (swCounterEigvalPlus t : ℂ) • swCounterEigvecPlus t := by
  have hsq_nn : 0 ≤ 1 + 4 * t ^ 2 := by positivity
  have hsqrt_sq : Real.sqrt (1 + 4 * t ^ 2) ^ 2 = 1 + 4 * t ^ 2 := Real.sq_sqrt hsq_nn
  have hpos : 0 < 1 + Real.sqrt (1 + 4 * t ^ 2) := by
    have : 0 ≤ Real.sqrt (1 + 4 * t ^ 2) := Real.sqrt_nonneg _
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hz
    have h0 := congrFun hz 0
    simp only [swCounterEigvecMinus, Matrix.cons_val_zero, Pi.zero_apply,
      Complex.ofReal_eq_zero, neg_eq_zero] at h0
    linarith
  · funext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, A10.swCounterH0_2x2, A10.swCounterV_2x2,
        swCounterEigvecMinus, swCounterEigvalMinus, Complex.real_smul]
      have hreal : t * (2 * t) =
          (1 - Real.sqrt (1 + 4 * t ^ 2)) / 2 * -(1 + Real.sqrt (1 + 4 * t ^ 2)) := by
        nlinarith [hsqrt_sq]
      have hC := congrArg (fun r : ℝ => (r : ℂ)) hreal
      push_cast at hC
      linear_combination hC
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, A10.swCounterH0_2x2, A10.swCounterV_2x2,
        swCounterEigvecMinus, swCounterEigvalMinus, Complex.real_smul]
      ring
  · intro hz
    have h1 := congrFun hz 1
    simp only [swCounterEigvecPlus, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply,
      Complex.ofReal_eq_zero] at h1
    linarith
  · funext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, A10.swCounterH0_2x2, A10.swCounterV_2x2,
        swCounterEigvecPlus, swCounterEigvalPlus, Complex.real_smul]
      ring
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, A10.swCounterH0_2x2, A10.swCounterV_2x2,
        swCounterEigvecPlus, swCounterEigvalPlus, Complex.real_smul]
      have hreal : t * (2 * t) + (1 + Real.sqrt (1 + 4 * t ^ 2)) =
          (1 + Real.sqrt (1 + 4 * t ^ 2)) / 2 * (1 + Real.sqrt (1 + 4 * t ^ 2)) := by
        nlinarith [hsqrt_sq]
      have hC := congrArg (fun r : ℝ => (r : ℂ)) hreal
      push_cast at hC
      linear_combination hC

/-- Exact finite-coupling non-equivalence at `t = 2 / 3` (`ex:ch21-sw-two-level`):
the lower exact eigenvalue is `E_-(2/3) = -1/3` (upper `4/3`), whereas the second-order effective
operator gives `(H_eff^{[2]}(2/3))_{00} = -4/9 ≠ -1/3`. -/
theorem swCounter_2x2_finite_coupling_discrepancy :
    swCounterEigvalMinus (2 / 3 : ℝ) = -1 / 3 ∧
    swCounterEigvalPlus (2 / 3 : ℝ) = 4 / 3 ∧
    (swEffPoly2 A10.swCounterP_2x2 A10.swCounterH0_2x2 A10.swCounterV_2x2
      A10.swCounterS1_2x2 (2 / 3 : ℝ)) 0 0 = (-4 / 9 : ℂ) ∧
    ((swCounterEigvalMinus (2 / 3 : ℝ) : ℝ) : ℂ) ≠
      (swEffPoly2 A10.swCounterP_2x2 A10.swCounterH0_2x2 A10.swCounterV_2x2
        A10.swCounterS1_2x2 (2 / 3 : ℝ)) 0 0 := by
  have hsqrt : Real.sqrt (1 + 4 * (2 / 3 : ℝ) ^ 2) = 5 / 3 := by
    rw [show (1 : ℝ) + 4 * (2 / 3 : ℝ) ^ 2 = (5 / 3 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 3)]
  have hminus : swCounterEigvalMinus (2 / 3 : ℝ) = -1 / 3 := by
    unfold swCounterEigvalMinus; rw [hsqrt]; norm_num
  have hplus : swCounterEigvalPlus (2 / 3 : ℝ) = 4 / 3 := by
    unfold swCounterEigvalPlus; rw [hsqrt]; norm_num
  have heff : (swEffPoly2 A10.swCounterP_2x2 A10.swCounterH0_2x2 A10.swCounterV_2x2
      A10.swCounterS1_2x2 (2 / 3 : ℝ)) 0 0 = (-4 / 9 : ℂ) := by
    rw [(swCounter_2x2_rotated_entries (2 / 3 : ℝ)).2.2]
    norm_num
  refine ⟨hminus, hplus, heff, ?_⟩
  rw [hminus, heff]
  norm_num

/-- Concrete instantiation of `prop:ch21-sw-analytic-remainder` on `ex:ch21-sw-two-level`:
`‖P R₃(t) P‖ ≤ ‖R₃(t)‖ ≤ (8 / 3) * |t|³` in the Euclidean `L2Operator` norm. -/
theorem swCounter_2x2_analytic_remainder_bound (t : ℝ) :
    let P := A10.swCounterP_2x2
    let H0 := A10.swCounterH0_2x2
    let V := A10.swCounterV_2x2
    let S1 := A10.swCounterS1_2x2
    P * swRotatedHam H0 V S1 t * P =
      swEffPoly2 P H0 V S1 t + P * swRemainder3 H0 V S1 t * P ∧
    ‖P * swRemainder3 H0 V S1 t * P‖ ≤ ‖swRemainder3 H0 V S1 t‖ ∧
    ‖swRemainder3 H0 V S1 t‖ ≤ (8 / 3 : ℝ) * |t| ^ 3 := by
  dsimp only
  let P := A10.swCounterP_2x2
  let Q := (1 : Matrix (Fin 2) (Fin 2) ℂ) - P
  let H0 := A10.swCounterH0_2x2
  let V := A10.swCounterV_2x2
  let S1 := A10.swCounterS1_2x2
  have hP := swCounterP_2x2_ortho
  have hPart : P + Q = 1 := by simp [Q]
  have hPQ : P * Q = 0 := by dsimp only [Q]; rw [mul_sub, mul_one, hP.1, sub_self]
  have hQP : Q * P = 0 := by dsimp only [Q]; rw [sub_mul, one_mul, hP.1, sub_self]
  have hSpp : P * S1 * P = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, P, S1, A10.swCounterP_2x2, A10.swCounterS1_2x2]
  have hGen : adOp S1 H0 = -(P * V * Q + Q * V * P) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [adOp, Matrix.mul_apply, Fin.sum_univ_two, P, Q, H0, V, S1,
        A10.swCounterP_2x2, A10.swCounterH0_2x2, A10.swCounterV_2x2, A10.swCounterS1_2x2]
  have hmain := swCompressed_exact_plus_remainder_and_bound P Q H0 V S1 t
    hP.1 hP.2 hPart hPQ hQP hSpp swCounterS1_2x2_skew hGen
  have had3 : adIter S1 3 H0 = (4 : ℝ) • V := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [adIter, adOp, Matrix.mul_apply, Fin.sum_univ_two, H0, V, S1,
        A10.swCounterH0_2x2, A10.swCounterV_2x2, A10.swCounterS1_2x2, Complex.real_smul]
  have had2 : adIter S1 2 V = (-4 : ℝ) • V := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [adIter, adOp, Matrix.mul_apply, Fin.sum_univ_two, V, S1,
        A10.swCounterV_2x2, A10.swCounterS1_2x2, Complex.real_smul]
  have hVunit : V ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Unitary.mem_iff]
    constructor <;> (ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        V, A10.swCounterV_2x2])
  have hVnorm : ‖V‖ = 1 := CStarRing.norm_coe_unitary ⟨V, hVunit⟩
  have h3norm : ‖adIter S1 3 H0‖ = 4 := by
    rw [had3, norm_smul, Real.norm_eq_abs, hVnorm]; norm_num
  have h2norm : ‖adIter S1 2 V‖ = 4 := by
    rw [had2, norm_smul, Real.norm_eq_abs, hVnorm]; norm_num
  refine ⟨hmain.1, hmain.2.1, ?_⟩
  have hb := hmain.2.2
  rw [h3norm, h2norm] at hb
  linarith

end TwoLevelWitness

/-! ## 3. Concrete `Ch21 → A10` Spinful Umklapp Block Analytic Remainder Bounds -/

section UmklappAnalyticBridge

noncomputable local instance localModeLinearOrderCh21Rem (h : ℕ) :
    LinearOrder (A05.Mode (Fin 4) h) := A05.speciesOrder h
noncomputable local instance localModeLTCh21Rem (h : ℕ) :
    LT (A05.Mode (Fin 4) h) := (A05.speciesOrder h).toLT
noncomputable local instance localModeLECh21Rem (h : ℕ) :
    LE (A05.Mode (Fin 4) h) := (A05.speciesOrder h).toLE
noncomputable local instance localModeDecidableEqCh21Rem (h : ℕ) :
    DecidableEq (A05.Mode (Fin 4) h) := A05.localModeDecidableEq h

/-- Bounded-operator bridge `A05.Operators SpinBranch h → (A05.FockSpace SpinBranch h →L[ℂ] ...)`. -/
noncomputable def toFockCLM (h : ℕ) (T : A05.Operators SpinBranch h) :
    A05.FockSpace SpinBranch h →L[ℂ] A05.FockSpace SpinBranch h :=
  LinearMap.toContinuousLinearMap T

lemma toFockCLM_add (h : ℕ) (A B : A05.Operators SpinBranch h) :
    toFockCLM h (A + B) = toFockCLM h A + toFockCLM h B := by
  ext v; rfl

lemma toFockCLM_sub (h : ℕ) (A B : A05.Operators SpinBranch h) :
    toFockCLM h (A - B) = toFockCLM h A - toFockCLM h B := by
  ext v; rfl

lemma toFockCLM_neg (h : ℕ) (A : A05.Operators SpinBranch h) :
    toFockCLM h (-A) = -toFockCLM h A := by
  ext v; rfl

lemma toFockCLM_zero (h : ℕ) :
    toFockCLM h (0 : A05.Operators SpinBranch h) = 0 := by
  ext v; rfl

lemma toFockCLM_one (h : ℕ) :
    toFockCLM h (1 : A05.Operators SpinBranch h) = 1 := by
  ext v; rfl

lemma toFockCLM_mul (h : ℕ) (A B : A05.Operators SpinBranch h) :
    toFockCLM h (A * B) = toFockCLM h A * toFockCLM h B := by
  ext v; rfl

lemma toFockCLM_smul_real (h : ℕ) (r : ℝ) (A : A05.Operators SpinBranch h) :
    toFockCLM h ((r : ℂ) • A) = r • toFockCLM h A := by
  ext v
  simp [toFockCLM, Complex.real_smul]

lemma toFockCLM_star (h : ℕ) (A : A05.Operators SpinBranch h) :
    star (toFockCLM h A) = toFockCLM h (LinearMap.adjoint A) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact (LinearMap.adjoint_toContinuousLinearMap A).symm

lemma toFockCLM_commutator (h : ℕ) (A B : A05.Operators SpinBranch h) :
    toFockCLM h (A02.commutator A B) = adOp (toFockCLM h A) (toFockCLM h B) := by
  simp [A02.commutator, adOp, toFockCLM_sub, toFockCLM_mul]

/-- Exact alignment of `swBchPoly2` with frozen `A10.bchSecondOrderPolynomial` under `toFockCLM`. -/
theorem toFockCLM_bchSecondOrderPolynomial (h : ℕ)
    (H0 V S1 : A05.Operators SpinBranch h) (t : ℝ) :
    toFockCLM h (A10.bchSecondOrderPolynomial h H0 V S1 t) =
      swBchPoly2 (toFockCLM h H0) (toFockCLM h V) (toFockCLM h S1) t := by
  unfold A10.bchSecondOrderPolynomial swBchPoly2
  have h2 : ((2 : ℂ)⁻¹) = (((2 : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have ht2 : ((t : ℂ) ^ 2) = (((t ^ 2 : ℝ) : ℂ)) := by push_cast; rfl
  rw [h2, ht2, toFockCLM_add, toFockCLM_add, toFockCLM_smul_real, toFockCLM_smul_real,
    toFockCLM_add, toFockCLM_add, toFockCLM_smul_real, toFockCLM_commutator,
    toFockCLM_commutator, toFockCLM_commutator, toFockCLM_commutator]
  rfl

/-- Exact alignment of `swEffPoly2` with frozen `A10.swEffectiveSecondOrder` under `toFockCLM`. -/
theorem toFockCLM_swEffectiveSecondOrder (h : ℕ)
    (P H0 V S1 : A05.Operators SpinBranch h) (t : ℝ) :
    toFockCLM h (A10.swEffectiveSecondOrder h P H0 V S1 t) =
      swEffPoly2 (toFockCLM h P) (toFockCLM h H0) (toFockCLM h V) (toFockCLM h S1) t := by
  unfold A10.swEffectiveSecondOrder A10.swSecondOrderCorrection swEffPoly2
  have h2 : ((2 : ℂ)⁻¹) = (((2 : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have ht2 : ((t : ℂ) ^ 2) = (((t ^ 2 : ℝ) : ℂ)) := by push_cast; rfl
  rw [h2, ht2, toFockCLM_add, toFockCLM_add, toFockCLM_smul_real, toFockCLM_smul_real,
    toFockCLM_smul_real, toFockCLM_mul, toFockCLM_mul, toFockCLM_mul, toFockCLM_mul,
    toFockCLM_mul, toFockCLM_mul, toFockCLM_commutator]

private lemma ket_prod_eq_rem (h : ℕ) (S : A05.Occupation SpinBranch h) :
    @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S = A02.ket S := by
  have hdec : (instDecidableEqProd : DecidableEq (A05.Mode SpinBranch h)) =
      A05.localModeDecidableEq h := Subsingleton.elim _ _
  exact congrArg (fun d => @A02.ket (A05.Mode SpinBranch h) _ d S) hdec

private lemma umklappTargetConfig_ne_ground0_rem (h : ℕ) (hh : 0 < h) :
    umklappTargetConfig h hh ≠ A05.groundConfiguration h (fun _ : SpinBranch => (0 : ℤ)) := by
  intro heq
  have h1 := umklappZeroChargeWitness_orthogonal_zero_budget h hh 0 _
    (A05.ground_mem_budget h hh (fun _ => 0) (zeroCharge_admissible h) 0)
  rw [umklappZeroChargeWitness, heq, ket_prod_eq_rem] at h1
  exact A05.ground_ne_zero h (fun _ : SpinBranch => (0 : ℤ)) (inner_self_eq_zero.mp h1)

private lemma umklappBlockVOp_ket_rem (h : ℕ) (hh : 0 < h) (gU : ℝ)
    (S : A05.Occupation SpinBranch h) :
    umklappBlockVOp h hh gU (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S) =
      if S = A05.groundConfiguration h (fun _ => 0) then
        (-((gU : ℂ) / ((2 * (h : ℂ)) ^ 2))) • umklappZeroChargeWitness h hh
      else if S = umklappTargetConfig h hh then
        (-((gU : ℂ) / ((2 * (h : ℂ)) ^ 2))) • A05.groundKet h (fun _ => 0)
      else 0 := by
  let S₀ : A05.Occupation SpinBranch h := A05.groundConfiguration h (fun _ => 0)
  let St := umklappTargetConfig h hh
  have hne : St ≠ S₀ := umklappTargetConfig_ne_ground0_rem h hh
  have hproj_exp (v : A05.FockSpace SpinBranch h) :
      umklappBlockProj h hh v =
        inner ℂ (A05.groundKet h (fun _ => 0)) v • A05.groundKet h (fun _ => 0) +
        inner ℂ (umklappZeroChargeWitness h hh) v • umklappZeroChargeWitness h hh := by
    apply (@A02.coordinates (A05.Mode SpinBranch h) _ instDecidableEqProd).injective
    funext T
    have hcoord (w : A05.FockSpace SpinBranch h) :
        @A02.coordinates (A05.Mode SpinBranch h) _ instDecidableEqProd w T =
          inner ℂ (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd T) w := by
      rw [@A02.fock_inner (A05.Mode SpinBranch h) _ instDecidableEqProd]
      simp [A02.ket_apply, A02.coordinates]
    rw [hcoord, ← LinearMap.adjoint_inner_left]
    have hadj : LinearMap.adjoint (umklappBlockProj h hh) = umklappBlockProj h hh :=
      @A03.projection_adjoint (A05.Mode SpinBranch h) _ instDecidableEqProd _
    rw [hadj, umklappBlockProj, @A03.projection_ket (A05.Mode SpinBranch h) _ instDecidableEqProd]
    rw [map_add, map_smul, map_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcoord,
      A05.groundKet, umklappZeroChargeWitness, ← ket_prod_eq_rem,
      @A02.ket_inner (A05.Mode SpinBranch h) _ instDecidableEqProd]
    by_cases hT0 : T = S₀
    · subst hT0; simp [hne.symm, S₀, St]
    · by_cases hTt : T = St
      · subst hTt; simp [hT0, S₀, St]
      · simp [hT0, hTt, S₀, St]
  have hVmat := umklappBlockVMatrix_explicit h hh gU
  have h00 : inner ℂ (A05.groundKet h (fun _ => 0))
      (periodicUmklappOp h gU (A05.groundKet h (fun _ => 0))) = 0 := by
    have := congrFun (congrFun hVmat 0) 0
    simpa [umklappBlockVMatrix, umklappBlockBasis] using this
  have h01 : inner ℂ (A05.groundKet h (fun _ => 0))
      (periodicUmklappOp h gU (umklappZeroChargeWitness h hh)) =
      -((gU : ℂ) / ((2 * (h : ℂ)) ^ 2)) := by
    have := congrFun (congrFun hVmat 0) 1
    simpa [umklappBlockVMatrix, umklappBlockBasis] using this
  have h10 : inner ℂ (umklappZeroChargeWitness h hh)
      (periodicUmklappOp h gU (A05.groundKet h (fun _ => 0))) =
      -((gU : ℂ) / ((2 * (h : ℂ)) ^ 2)) := by
    have := congrFun (congrFun hVmat 1) 0
    simpa [umklappBlockVMatrix, umklappBlockBasis] using this
  have h11 : inner ℂ (umklappZeroChargeWitness h hh)
      (periodicUmklappOp h gU (umklappZeroChargeWitness h hh)) = 0 := by
    have := congrFun (congrFun hVmat 1) 1
    simpa [umklappBlockVMatrix, umklappBlockBasis] using this
  change umklappBlockProj h hh (periodicUmklappOp h gU (umklappBlockProj h hh
      (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S))) = _
  rw [umklappBlockProj, @A03.projection_ket (A05.Mode SpinBranch h) _ instDecidableEqProd]
  by_cases hS0 : S = S₀
  · subst hS0
    simp only [Set.mem_insert_iff, true_or, ↓reduceIte, S₀]
    rw [ket_prod_eq_rem, ← A05.groundKet, ← umklappBlockProj, hproj_exp, h00, h10]
    simp
  · by_cases hSt : S = St
    · subst hSt
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true, ↓reduceIte, hS0, S₀, St]
      rw [← umklappZeroChargeWitness, ← umklappBlockProj, hproj_exp, h01, h11]
      simp
    · simp [hS0, hSt, S₀, St]

private lemma umklappBlockVOp_self_adjoint_rem (h : ℕ) (hh : 0 < h) (gU : ℝ) :
    LinearMap.adjoint (umklappBlockVOp h hh gU) = umklappBlockVOp h hh gU := by
  unfold umklappBlockVOp
  have hPi : LinearMap.adjoint (umklappBlockProj h hh) = umklappBlockProj h hh :=
    @A03.projection_adjoint (A05.Mode SpinBranch h) _ instDecidableEqProd _
  have hU : LinearMap.adjoint (periodicUmklappOp h gU) = periodicUmklappOp h gU :=
    umklappOp_self_adjoint h _ gU
  rw [show ∀ X Y : A05.Operators SpinBranch h,
      LinearMap.adjoint (X * Y) = LinearMap.adjoint Y * LinearMap.adjoint X from
      fun X Y => LinearMap.adjoint_comp X Y,
    show ∀ X Y : A05.Operators SpinBranch h,
      LinearMap.adjoint (X * Y) = LinearMap.adjoint Y * LinearMap.adjoint X from
      fun X Y => LinearMap.adjoint_comp X Y,
    hPi, hU, mul_assoc]

/-- Exact Hilbert-space operator norm of the spinful Umklapp block perturbation on
`A05.FockSpace SpinBranch h`: `‖umklappBlockVOp h hh gU‖ = |g_U| / (4 h²)`. -/
theorem norm_toFockCLM_umklappBlockVOp (h : ℕ) (hh : 0 < h) (gU : ℝ) :
    ‖toFockCLM h (umklappBlockVOp h hh gU)‖ = |gU| / (4 * (h : ℝ) ^ 2) := by
  let S₀ : A05.Occupation SpinBranch h := A05.groundConfiguration h (fun _ => 0)
  let St := umklappTargetConfig h hh
  have hne : St ≠ S₀ := umklappTargetConfig_ne_ground0_rem h hh
  let cR : ℝ := -(gU / (4 * (h : ℝ) ^ 2))
  have hcC : (-((gU : ℂ) / ((2 * (h : ℂ)) ^ 2))) = (cR : ℂ) := by
    dsimp only [cR]; push_cast; ring
  have hVsq : umklappBlockVOp h hh gU * umklappBlockVOp h hh gU =
      ((cR ^ 2 : ℝ) : ℂ) • umklappBlockProj h hh := by
    apply @A02.end_ext_basis (A05.Mode SpinBranch h) _ instDecidableEqProd
    intro S
    simp only [Module.End.mul_apply, LinearMap.smul_apply, umklappBlockVOp_ket_rem, hcC,
      umklappBlockProj, @A03.projection_ket (A05.Mode SpinBranch h) _ instDecidableEqProd]
    by_cases hS0 : S = S₀
    · subst hS0
      simp only [↓reduceIte, Set.mem_insert_iff, true_or, S₀]
      rw [map_smul, umklappZeroChargeWitness, umklappBlockVOp_ket_rem, hcC,
        ite_eq_right hne, ite_eq_left rfl, smul_smul, A05.groundKet, ← ket_prod_eq_rem]
      push_cast; ring_nf
    · by_cases hSt : S = St
      · subst hSt
        simp only [hS0, ↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff, or_true, S₀, St]
        rw [map_smul, A05.groundKet, ← ket_prod_eq_rem, umklappBlockVOp_ket_rem, hcC,
          ite_eq_left rfl, smul_smul, umklappZeroChargeWitness]
        push_cast; ring_nf
      · simp [hS0, hSt, S₀, St]
  have hPi_id : toFockCLM h (umklappBlockProj h hh) * toFockCLM h (umklappBlockProj h hh) =
      toFockCLM h (umklappBlockProj h hh) := by
    rw [← toFockCLM_mul, umklappBlockProj,
      @A03.projection_idempotent (A05.Mode SpinBranch h) _ instDecidableEqProd _]
  have hPi_star : star (toFockCLM h (umklappBlockProj h hh)) = toFockCLM h (umklappBlockProj h hh) := by
    rw [toFockCLM_star, umklappBlockProj,
      @A03.projection_adjoint (A05.Mode SpinBranch h) _ instDecidableEqProd _]
  have hPi_le : ‖toFockCLM h (umklappBlockProj h hh)‖ ≤ 1 :=
    norm_ortho_proj_le_one hPi_id hPi_star
  have hPi_ge : 1 ≤ ‖toFockCLM h (umklappBlockProj h hh)‖ := by
    let v₀ := @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S₀
    have hv₀_norm : ‖v₀‖ = 1 := by
      have h1 : inner ℂ v₀ v₀ = 1 := by
        rw [@A02.ket_inner (A05.Mode SpinBranch h) _ instDecidableEqProd]; simp
      have hsq : ‖v₀‖ ^ 2 = 1 := by
        rw [inner_self_eq_norm_sq_to_K] at h1
        exact Complex.ofReal_injective (by simpa using h1)
      nlinarith [norm_nonneg v₀]
    have hfix : toFockCLM h (umklappBlockProj h hh) v₀ = v₀ := by
      change umklappBlockProj h hh v₀ = v₀
      rw [umklappBlockProj, @A03.projection_ket (A05.Mode SpinBranch h) _ instDecidableEqProd]
      simp [S₀, v₀]
    have hle := (toFockCLM h (umklappBlockProj h hh)).le_opNorm v₀
    rw [hfix, hv₀_norm, mul_one] at hle
    exact hle
  have hPi_norm : ‖toFockCLM h (umklappBlockProj h hh)‖ = 1 := le_antisymm hPi_le hPi_ge
  have hVstar : star (toFockCLM h (umklappBlockVOp h hh gU)) =
      toFockCLM h (umklappBlockVOp h hh gU) := by
    rw [toFockCLM_star, umklappBlockVOp_self_adjoint_rem]
  have hsq : ‖toFockCLM h (umklappBlockVOp h hh gU)‖ ^ 2 = cR ^ 2 := by
    calc
      ‖toFockCLM h (umklappBlockVOp h hh gU)‖ ^ 2
        = ‖toFockCLM h (umklappBlockVOp h hh gU)‖ * ‖toFockCLM h (umklappBlockVOp h hh gU)‖ := sq _
      _ = ‖star (toFockCLM h (umklappBlockVOp h hh gU)) *
            toFockCLM h (umklappBlockVOp h hh gU)‖ :=
            (CStarRing.norm_star_mul_self).symm
      _ = ‖toFockCLM h (umklappBlockVOp h hh gU * umklappBlockVOp h hh gU)‖ := by
            rw [hVstar, ← toFockCLM_mul]
      _ = ‖(cR ^ 2) • toFockCLM h (umklappBlockProj h hh)‖ := by
            rw [hVsq, toFockCLM_smul_real]
      _ = cR ^ 2 := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg cR), hPi_norm, mul_one]
  have habs_cR : |cR| = |gU| / (4 * (h : ℝ) ^ 2) := by
    dsimp only [cR]
    rw [abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * (h : ℝ) ^ 2)]
  rw [← habs_cR]
  nlinarith [norm_nonneg (toFockCLM h (umklappBlockVOp h hh gU)), abs_nonneg cR, sq_abs cR]

/-- Exact iterated adjoint commutators on the spinful Umklapp block operator algebra:
`ad_{S₁}²(V) = (-4 s²) • V` and `ad_{S₁}³(H₀) = (4 s²) • V` where `s = -g_U / (8 h³)`. -/
theorem umklappBlock_iterated_ad (h : ℕ) (hh : 0 < h) (gU : ℝ) :
    let H0 := toFockCLM h (spinfulFreeHamiltonian h)
    let V := toFockCLM h (umklappBlockVOp h hh gU)
    let S1 := toFockCLM h (umklappBlockS1Op h hh gU)
    let sR : ℝ := -(gU / (8 * (h : ℝ) ^ 3))
    adIter S1 2 V = (-(4 * sR ^ 2)) • V ∧
    adIter S1 3 H0 = (4 * sR ^ 2) • V := by
  dsimp only
  let S₀ : A05.Occupation SpinBranch h := A05.groundConfiguration h (fun _ => 0)
  let St := umklappTargetConfig h hh
  have hne : St ≠ S₀ := umklappTargetConfig_ne_ground0_rem h hh
  let c : ℂ := -((gU : ℂ) / ((2 * (h : ℂ)) ^ 2))
  let s : ℂ := c / (2 * (h : ℂ))
  let sR : ℝ := -(gU / (8 * (h : ℝ) ^ 3))
  have hs_eq : s = (sR : ℂ) := by
    dsimp only [s, c, sR]; push_cast; ring
  let v₀ : A05.FockSpace SpinBranch h := A05.groundKet h (fun _ : SpinBranch => (0 : ℤ))
  let vt : A05.FockSpace SpinBranch h := umklappZeroChargeWitness h hh
  have hS1ket (S : A05.Occupation SpinBranch h) :
      umklappBlockS1Op h hh gU (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S) =
        if S = S₀ then s • vt else if S = St then (-s) • v₀ else 0 :=
    @A02.extend_basis_ket (A05.Mode SpinBranch h) _ instDecidableEqProd _ S
  have hVket (S : A05.Occupation SpinBranch h) :
      umklappBlockVOp h hh gU (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S) =
        if S = S₀ then c • vt else if S = St then c • v₀ else 0 :=
    umklappBlockVOp_ket_rem h hh gU S
  have hS1_0 : umklappBlockS1Op h hh gU v₀ = s • vt := by
    rw [show v₀ = @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S₀ from
      (ket_prod_eq_rem h S₀).symm, hS1ket]
    simp
  have hS1_t : umklappBlockS1Op h hh gU vt = (-s) • v₀ := by
    rw [show vt = @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd St from rfl, hS1ket]
    simp [hne]
  have hV_0 : umklappBlockVOp h hh gU v₀ = c • vt := by
    rw [show v₀ = @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S₀ from
      (ket_prod_eq_rem h S₀).symm, hVket]
    simp
  have hV_t : umklappBlockVOp h hh gU vt = c • v₀ := by
    rw [show vt = @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd St from rfl, hVket]
    simp [hne]
  have hS1V_ket (S : A05.Occupation SpinBranch h) :
      A02.commutator (umklappBlockS1Op h hh gU) (umklappBlockVOp h hh gU)
        (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S) =
        if S = S₀ then (-(2 * c * s)) • v₀ else if S = St then (2 * c * s) • vt else 0 := by
    simp only [A02.commutator, LinearMap.sub_apply, Module.End.mul_apply, hVket, hS1ket]
    by_cases hS0 : S = S₀
    · subst hS0
      simp only [↓reduceIte, map_smul, hS1_t, hV_t, smul_smul]
      rw [← sub_smul]; congr 1; ring
    · by_cases hSt : S = St
      · subst hSt
        simp only [hS0, ↓reduceIte, map_smul, hS1_0, hV_0, smul_smul]
        rw [← sub_smul]; congr 1; ring
      · simp [hS0, hSt]
  have hS1V_0 : A02.commutator (umklappBlockS1Op h hh gU) (umklappBlockVOp h hh gU) v₀ =
      (-(2 * c * s)) • v₀ := by
    have hv : v₀ = @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S₀ :=
      (ket_prod_eq_rem h S₀).symm
    conv_lhs => rw [hv]
    rw [hS1V_ket]; simp
  have hS1V_t : A02.commutator (umklappBlockS1Op h hh gU) (umklappBlockVOp h hh gU) vt =
      (2 * c * s) • vt := by
    have hv : vt = @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd St := rfl
    conv_lhs => rw [hv]
    rw [hS1V_ket]; simp [hne]
  have had2_lin :
      A02.commutator (umklappBlockS1Op h hh gU)
        (A02.commutator (umklappBlockS1Op h hh gU) (umklappBlockVOp h hh gU)) =
        ((-(4 * sR ^ 2) : ℝ) : ℂ) • umklappBlockVOp h hh gU := by
    apply @A02.end_ext_basis (A05.Mode SpinBranch h) _ instDecidableEqProd
    intro S
    change umklappBlockS1Op h hh gU
        (A02.commutator (umklappBlockS1Op h hh gU) (umklappBlockVOp h hh gU)
          (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S)) -
      A02.commutator (umklappBlockS1Op h hh gU) (umklappBlockVOp h hh gU)
        (umklappBlockS1Op h hh gU (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S)) =
      ((-(4 * sR ^ 2) : ℝ) : ℂ) •
        umklappBlockVOp h hh gU (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S)
    rw [hS1V_ket, hS1ket, hVket]
    by_cases hS0 : S = S₀
    · subst hS0
      simp only [↓reduceIte, map_smul, hS1_0, hS1V_t, smul_smul]
      rw [← sub_smul, hs_eq]
      congr 1; push_cast; ring
    · by_cases hSt : S = St
      · subst hSt
        simp only [hS0, ↓reduceIte, map_smul, hS1_t, hS1V_0, smul_smul]
        rw [← sub_smul, hs_eq]
        congr 1; push_cast; ring
      · simp [hS0, hSt]
  have had2_clm :
      adIter (toFockCLM h (umklappBlockS1Op h hh gU)) 2 (toFockCLM h (umklappBlockVOp h hh gU)) =
        (-(4 * sR ^ 2)) • toFockCLM h (umklappBlockVOp h hh gU) := by
    change adOp (toFockCLM h (umklappBlockS1Op h hh gU))
        (adOp (toFockCLM h (umklappBlockS1Op h hh gU)) (toFockCLM h (umklappBlockVOp h hh gU))) = _
    rw [← toFockCLM_commutator, ← toFockCLM_commutator, had2_lin, toFockCLM_smul_real]
  have hS1H0_eq : A02.commutator (umklappBlockS1Op h hh gU) (spinfulFreeHamiltonian h) =
      -umklappBlockVOp h hh gU := by
    apply @A02.end_ext_basis (A05.Mode SpinBranch h) _ instDecidableEqProd
    intro S
    simp only [A02.commutator, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply,
      hS1ket, hVket]
    have hhC : (h : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hh)
    by_cases hS0 : S = S₀
    · subst hS0
      have hH0_0 : spinfulFreeHamiltonian h (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S₀) = 0 := by
        rw [ket_prod_eq_rem]; exact spinfulFreeHamiltonian_ground_zero h hh
      have hH0_t : spinfulFreeHamiltonian h vt = (2 * (h : ℂ)) • vt :=
        spinfulFreeHamiltonian_umklappWitness h hh
      simp only [↓reduceIte, hH0_0, map_zero, map_smul, hH0_t, smul_smul, zero_sub]
      rw [← neg_smul, ← neg_smul]
      congr 1
      dsimp only [s]
      field_simp [hhC]
    · by_cases hSt : S = St
      · subst hSt
        have hH0_0 : spinfulFreeHamiltonian h v₀ = 0 := spinfulFreeHamiltonian_ground_zero h hh
        have hH0_t : spinfulFreeHamiltonian h (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd St) =
            (2 * (h : ℂ)) • vt :=
          spinfulFreeHamiltonian_umklappWitness h hh
        simp only [hS0, ↓reduceIte, hH0_t, map_smul, hS1_t, hH0_0, smul_zero, sub_zero, smul_smul]
        rw [← neg_smul]
        congr 1
        dsimp only [s]
        field_simp [hhC]
      · have hdiag : spinfulFreeHamiltonian h (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S) =
            ((∑ ν : SpinBranch, Ch07.relativeEnergy h (Ch07.speciesConfiguration h S ν) : ℤ) : ℂ) •
              @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S := by
          unfold spinfulFreeHamiltonian
          exact @A03.diagonal_ket (A05.Mode SpinBranch h) _ instDecidableEqProd _ S
        simp only [hS0, hSt, ↓reduceIte, hdiag, map_smul, hS1ket, smul_zero, map_zero, sub_zero,
          neg_zero]
  refine ⟨had2_clm, ?_⟩
  change adOp (toFockCLM h (umklappBlockS1Op h hh gU))
      (adOp (toFockCLM h (umklappBlockS1Op h hh gU))
        (adOp (toFockCLM h (umklappBlockS1Op h hh gU))
          (toFockCLM h (spinfulFreeHamiltonian h)))) = _
  rw [← toFockCLM_commutator, hS1H0_eq, toFockCLM_neg]
  have had_neg : ∀ X Y : A05.FockSpace SpinBranch h →L[ℂ] A05.FockSpace SpinBranch h,
      adOp X (-Y) = -adOp X Y := by
    intro X Y
    ext v
    simp [adOp]
    abel
  rw [had_neg, had_neg]
  change -adIter (toFockCLM h (umklappBlockS1Op h hh gU)) 2 (toFockCLM h (umklappBlockVOp h hh gU)) = _
  rw [had2_clm]
  module

/-- Operator-level `Ch21 → A10` analytic Schrieffer-Wolff remainder bound directly instantiating
`prop:ch21-sw-analytic-remainder` on `umklappBlock_a10_bch_bridge` in
`A05.FockSpace SpinBranch h →L[ℂ] A05.FockSpace SpinBranch h`:
- exact compressed rotation equals `toFockCLM (A10.swEffectiveSecondOrder ...) + P R₃(t) P`;
- exact operator-norm bound `‖P R₃(t) P‖ ≤ ‖R₃(t)‖ ≤ |t|³ |g_U|³ / (96 h⁸)` for every `0 < h`. -/
theorem umklappBlock_analytic_remainder_bound (h : ℕ) (hh : 0 < h) (gU t : ℝ) :
    let P_op := Ch14.projection h (fun _ : SpinBranch => (0 : ℤ)) 0
    let H0_op := spinfulFreeHamiltonian h
    let V_op := umklappBlockVOp h hh gU
    let S1_op := umklappBlockS1Op h hh gU
    let P := toFockCLM h P_op
    let H0 := toFockCLM h H0_op
    let V := toFockCLM h V_op
    let S1 := toFockCLM h S1_op
    P * swRotatedHam H0 V S1 t * P =
      toFockCLM h (A10.swEffectiveSecondOrder h P_op H0_op V_op S1_op t) +
        P * swRemainder3 H0 V S1 t * P ∧
    ‖P * swRemainder3 H0 V S1 t * P‖ ≤ ‖swRemainder3 H0 V S1 t‖ ∧
    ‖swRemainder3 H0 V S1 t‖ ≤ |t| ^ 3 * |gU| ^ 3 / (96 * (h : ℝ) ^ 8) := by
  dsimp only
  let P_op := Ch14.projection h (fun _ : SpinBranch => (0 : ℤ)) 0
  let H0_op := spinfulFreeHamiltonian h
  let V_op := umklappBlockVOp h hh gU
  let S1_op := umklappBlockS1Op h hh gU
  let P := toFockCLM h P_op
  let H0 := toFockCLM h H0_op
  let V := toFockCLM h V_op
  let S1 := toFockCLM h S1_op
  have hbridge := umklappBlock_a10_bch_bridge h hh gU t
  have hP_id_op : P_op * P_op = P_op := by
    dsimp only [P_op, Ch14.projection]
    exact @A03.projection_idempotent (A05.Mode SpinBranch h) _ (Ch14.localModeDecidableEq h) _
  have hP_adj_op : LinearMap.adjoint P_op = P_op := by
    dsimp only [P_op, Ch14.projection]
    exact @A03.projection_adjoint (A05.Mode SpinBranch h) _ (Ch14.localModeDecidableEq h) _
  have hP_id : P * P = P := by rw [← toFockCLM_mul, hP_id_op]
  have hP_star : star P = P := by rw [toFockCLM_star, hP_adj_op]
  have hS1_skew : star S1 = -S1 := by rw [toFockCLM_star, hbridge.2.1, toFockCLM_neg]
  have hrem_eq : P * swRotatedHam H0 V S1 t * P =
      toFockCLM h (A10.swEffectiveSecondOrder h P_op H0_op V_op S1_op t) +
        P * swRemainder3 H0 V S1 t * P := by
    have hbch_clm : P * swBchPoly2 H0 V S1 t * P =
        toFockCLM h (A10.swEffectiveSecondOrder h P_op H0_op V_op S1_op t) := by
      dsimp only [P, H0, V, S1]
      rw [← toFockCLM_bchSecondOrderPolynomial, ← toFockCLM_mul, ← toFockCLM_mul,
        hbridge.2.2.2.1]
    unfold swRemainder3
    calc
      P * swRotatedHam H0 V S1 t * P
        = P * (swBchPoly2 H0 V S1 t + (swRotatedHam H0 V S1 t - swBchPoly2 H0 V S1 t)) * P := by
          simp
      _ = P * swBchPoly2 H0 V S1 t * P +
          P * (swRotatedHam H0 V S1 t - swBchPoly2 H0 V S1 t) * P := by
          simp only [mul_add, add_mul]
      _ = toFockCLM h (A10.swEffectiveSecondOrder h P_op H0_op V_op S1_op t) +
          P * (swRotatedHam H0 V S1 t - swBchPoly2 H0 V S1 t) * P := by
          rw [hbch_clm]
  have hcomp : ‖P * swRemainder3 H0 V S1 t * P‖ ≤ ‖swRemainder3 H0 V S1 t‖ :=
    norm_compress_le_of_ortho_proj hP_id hP_star _
  have hbd := swRemainder3_norm_bound H0 V hS1_skew t
  have had := umklappBlock_iterated_ad h hh gU
  have hVnorm := norm_toFockCLM_umklappBlockVOp h hh gU
  let sR : ℝ := -(gU / (8 * (h : ℝ) ^ 3))
  have h4s2_nn : 0 ≤ 4 * sR ^ 2 := by positivity
  have hscale : 4 * sR ^ 2 * (|gU| / (4 * (h : ℝ) ^ 2)) = |gU| ^ 3 / (64 * (h : ℝ) ^ 8) := by
    dsimp only [sR]
    have hsq : gU ^ 2 = |gU| ^ 2 := (sq_abs gU).symm
    have hhne : (h : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hh)
    field_simp [hhne]
    rw [hsq]
    ring
  have h3norm : ‖adIter S1 3 H0‖ = |gU| ^ 3 / (64 * (h : ℝ) ^ 8) := by
    rw [had.2, norm_smul, Real.norm_eq_abs, abs_of_nonneg h4s2_nn, hVnorm]
    exact hscale
  have h2norm : ‖adIter S1 2 V‖ = |gU| ^ 3 / (64 * (h : ℝ) ^ 8) := by
    rw [had.1, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg h4s2_nn, hVnorm]
    exact hscale
  refine ⟨hrem_eq, hcomp, ?_⟩
  rw [h3norm, h2norm] at hbd
  calc
    ‖swRemainder3 H0 V S1 t‖
      ≤ |t| ^ 3 * (|gU| ^ 3 / (64 * (h : ℝ) ^ 8) / 6 + |gU| ^ 3 / (64 * (h : ℝ) ^ 8) / 2) := hbd
    _ = |t| ^ 3 * |gU| ^ 3 / (96 * (h : ℝ) ^ 8) := by ring

/-- Concrete `h = 2` specialization of the operator-level spinful Umklapp analytic remainder bound:
`‖P R₃(t) P‖ ≤ ‖R₃(t)‖ ≤ |t|³ |g_U|³ / 24576`. -/
theorem umklappBlock_analytic_remainder_bound_h2 (gU t : ℝ) :
    let P_op := Ch14.projection 2 (fun _ : SpinBranch => (0 : ℤ)) 0
    let H0_op := spinfulFreeHamiltonian 2
    let V_op := umklappBlockVOp 2 (by decide) gU
    let S1_op := umklappBlockS1Op 2 (by decide) gU
    let P := toFockCLM 2 P_op
    let H0 := toFockCLM 2 H0_op
    let V := toFockCLM 2 V_op
    let S1 := toFockCLM 2 S1_op
    ‖P * swRemainder3 H0 V S1 t * P‖ ≤ ‖swRemainder3 H0 V S1 t‖ ∧
    ‖swRemainder3 H0 V S1 t‖ ≤ |t| ^ 3 * |gU| ^ 3 / 24576 := by
  have hb := umklappBlock_analytic_remainder_bound 2 (by decide) gU t
  refine ⟨hb.2.1, ?_⟩
  convert hb.2.2 using 1
  norm_num

end UmklappAnalyticBridge

end Bosonize.Ch21
