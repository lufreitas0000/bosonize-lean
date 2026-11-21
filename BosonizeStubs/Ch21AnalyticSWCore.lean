module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Chapter 21 Leaf Module: Abstract Finite Analytic Schrieffer-Wolff Remainder (`prop:ch21-sw-analytic-remainder`)

Pure-Mathlib Lean 4 `module` formalizing the abstract finite-dimensional analytic Schrieffer-Wolff
Taylor remainder (`prop:ch21-sw-analytic-remainder`, `eq:ch21-rem-definition`,
`eq:ch21-sw-exact-plus-remainder`, `eq:ch21-sw-integral-remainder`, `eq:ch21-sw-norm-bound`) and
Euler trigonometric exponential formula on any unital Banach `CStarRing` (instantiating
simultaneously on `Matrix ι ι ℂ` with the Euclidean `L2Operator` norm and on bounded operators
`E →L[ℂ] E` over any finite-dimensional complex Hilbert space `E`).

This file is kept as a zero-`Bosonize`-dependency `module` (following the pattern of
`Bosonize/Core/V1S5FiniteVectorStates.lean`) so that `BosonizeStubs/Ch21AnalyticRemainder.lean`
imports all required `Mathlib` analysis packages cleanly through the Lean 4 module boundary with
zero Lake module-system warnings (`lake --wfail build BosonizeStubs` exit `0`).
-/

@[expose] public section

namespace Bosonize.Ch21

/-! ## 1. Abstract Finite Analytic Schrieffer-Wolff Remainder (`prop:ch21-sw-analytic-remainder`) -/

section AbstractAnalyticSWDefs

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Operator commutator `ad_{S₁}(T) = S₁ * T - T * S₁`. -/
def adOp (S1 T : A) : A :=
  S1 * T - T * S1

/-- Iterated adjoint commutator `ad_{S₁}^n(T)`. -/
def adIter (S1 : A) : ℕ → A → A
  | 0, T => T
  | n + 1, T => adOp S1 (adIter S1 n T)

/-- One-parameter conjugation flow `𝒰_r(T) = exp(r S₁) * T * exp(-r S₁)`. -/
noncomputable def swAdjointFlow (S1 : A) (r : ℝ) (T : A) : A :=
  NormedSpace.exp (r • S1) * T * NormedSpace.exp ((-r) • S1)

/-- Exact rotated Hamiltonian `H̃(t) = 𝒰_t(H₀ + t V)`. -/
noncomputable def swRotatedHam (H0 V S1 : A) (t : ℝ) : A :=
  swAdjointFlow S1 t (H0 + t • V)

/-- Degree-2 BCH polynomial `B₂(t)` matching `A10.bchSecondOrderPolynomial`. -/
noncomputable def swBchPoly2 (H0 V S1 : A) (t : ℝ) : A :=
  H0 + t • (V + adOp S1 H0) + (t ^ 2) • (adOp S1 V + (2 : ℝ)⁻¹ • adIter S1 2 H0)

/-- Compressed second-order effective Hamiltonian `H_eff^{[2]}(t)` matching
`A10.swEffectiveSecondOrder`. -/
noncomputable def swEffPoly2 (P H0 V S1 : A) (t : ℝ) : A :=
  P * H0 * P + t • (P * V * P) + (t ^ 2) • ((2 : ℝ)⁻¹ • (P * adOp S1 V * P))

/-- Analytic Schrieffer-Wolff Taylor remainder `R₃(t) := H̃(t) - B₂(t)` (`eq:ch21-rem-definition`). -/
noncomputable def swRemainder3 (H0 V S1 : A) (t : ℝ) : A :=
  swRotatedHam H0 V S1 t - swBchPoly2 H0 V S1 t

@[simp] lemma swAdjointFlow_zero (S1 T : A) :
    swAdjointFlow S1 0 T = T := by
  simp [swAdjointFlow]

lemma swAdjointFlow_add (S1 : A) (r : ℝ) (T₁ T₂ : A) :
    swAdjointFlow S1 r (T₁ + T₂) = swAdjointFlow S1 r T₁ + swAdjointFlow S1 r T₂ := by
  simp only [swAdjointFlow, mul_add, add_mul]

lemma swAdjointFlow_smul (S1 : A) (r c : ℝ) (T : A) :
    swAdjointFlow S1 r (c • T) = c • swAdjointFlow S1 r T := by
  simp only [swAdjointFlow, mul_smul_comm, smul_mul_assoc]

/-- Algebraic degree-2 compressed BCH identity in any normed `ℝ`-algebra (matching
`A10.sw_compressed_bch_second_order`). -/
theorem swBchPoly2_compressed (P Q H0 V S1 : A) (t : ℝ)
    (hP : P * P = P) (hPartition : P + Q = 1) (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (hSpp : P * S1 * P = 0)
    (hGenerator : adOp S1 H0 = -(P * V * Q + Q * V * P)) :
    P * swBchPoly2 H0 V S1 t * P = swEffPoly2 P H0 V S1 t := by
  let Voff : A := P * V * Q + Q * V * P
  have hl : P * S1 * Q = P * S1 := by
    calc
      P * S1 * Q = P * S1 * P + P * S1 * Q := by rw [hSpp, zero_add]
      _ = P * S1 * (P + Q) := by rw [mul_add]
      _ = P * S1 := by rw [hPartition, mul_one]
  have hr : Q * S1 * P = S1 * P := by
    calc
      Q * S1 * P = P * S1 * P + Q * S1 * P := by rw [hSpp, zero_add]
      _ = (P + Q) * S1 * P := by rw [add_mul, add_mul]
      _ = S1 * P := by rw [hPartition, one_mul]
  have hor : Voff * P = Q * V * P := by
    dsimp only [Voff]
    rw [add_mul]
    have hz : P * V * Q * P = 0 := by rw [mul_assoc, mul_assoc, hQP, mul_zero, mul_zero]
    rw [hz, zero_add, mul_assoc, hP]
  have hol : P * Voff = P * V * Q := by
    dsimp only [Voff]
    rw [mul_add]
    have h1 : P * (P * V * Q) = P * V * Q := by simp only [← mul_assoc, hP]
    have h2 : P * (Q * V * P) = 0 := by simp only [← mul_assoc, hPQ, zero_mul]
    rw [h1, h2, add_zero]
  have hoz : P * Voff * P = 0 := by
    rw [hol, mul_assoc, mul_assoc, hQP, mul_zero, mul_zero]
  have hleft : P * S1 * Voff * P = P * S1 * V * P := by
    calc
      P * S1 * Voff * P = P * S1 * (Voff * P) := by simp only [mul_assoc]
      _ = P * S1 * (Q * V * P) := by rw [hor]
      _ = (P * S1 * Q) * V * P := by simp only [mul_assoc]
      _ = P * S1 * V * P := by rw [hl]
  have hright : P * Voff * S1 * P = P * V * S1 * P := by
    rw [hol]
    calc
      P * V * Q * S1 * P = P * V * (Q * S1 * P) := by simp only [mul_assoc]
      _ = P * V * (S1 * P) := by rw [hr]
      _ = P * V * S1 * P := by simp only [mul_assoc]
  have hc : P * adOp S1 Voff * P = P * adOp S1 V * P := by
    simp only [adOp, mul_sub, sub_mul, ← mul_assoc, hleft, hright]
  have hn : adOp S1 (-Voff) = -adOp S1 Voff := by
    simp only [adOp, mul_neg, neg_mul, sub_neg_eq_add, neg_sub]
    rw [add_comm, sub_eq_add_neg]
  have hlin : P * (V + adOp S1 H0) * P = P * V * P := by
    rw [hGenerator]
    change P * (V + -Voff) * P = P * V * P
    simp only [mul_add, add_mul, mul_neg, neg_mul, hoz, neg_zero, add_zero]
  have hquad : P * (adOp S1 V + (2 : ℝ)⁻¹ • adIter S1 2 H0) * P =
      (2 : ℝ)⁻¹ • (P * adOp S1 V * P) := by
    change P * (adOp S1 V + (2 : ℝ)⁻¹ • adOp S1 (adOp S1 H0)) * P = _
    rw [hGenerator]
    change P * (adOp S1 V + (2 : ℝ)⁻¹ • adOp S1 (-Voff)) * P = _
    rw [hn]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_neg, neg_mul, hc]
    module
  have hdist (X Y Z : A) (a b : ℝ) :
      P * (X + a • Y + b • Z) * P = P * X * P + a • (P * Y * P) + b • (P * Z * P) := by
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  unfold swBchPoly2 swEffPoly2
  rw [hdist, hlin, hquad]

end AbstractAnalyticSWDefs

section AbstractAnalyticSWCalculus

variable {A : Type*} [NormedRing A] [CompleteSpace A] [NormedAlgebra ℝ A]

private lemma hasDerivAt_one_sub (u : ℝ) :
    HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (-1) u := by
  have h : HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (0 - 1) u :=
    (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)
  simpa using h

/-- Derivative of the adjoint flow `d/dr 𝒰_r(T) = 𝒰_r([S₁, T])`. -/
lemma hasDerivAt_swAdjointFlow (S1 T : A) (r : ℝ) :
    HasDerivAt (fun s : ℝ => swAdjointFlow S1 s T) (swAdjointFlow S1 r (adOp S1 T)) r := by
  have h1 : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • S1))
      (NormedSpace.exp (r • S1) * S1) r :=
    hasDerivAt_exp_smul_const S1 r
  have h2 : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • (-S1)))
      ((-S1) * NormedSpace.exp (r • (-S1))) r :=
    hasDerivAt_exp_smul_const' (-S1) r
  have h2' : HasDerivAt (fun s : ℝ => NormedSpace.exp ((-s) • S1))
      ((-S1) * NormedSpace.exp ((-r) • S1)) r := by
    have heq : (fun s : ℝ => NormedSpace.exp (s • (-S1))) =
        (fun s : ℝ => NormedSpace.exp ((-s) • S1)) := by
      funext s; rw [smul_neg, ← neg_smul]
    rw [heq, smul_neg, ← neg_smul] at h2
    exact h2
  have h1T : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • S1) * T)
      ((NormedSpace.exp (r • S1) * S1) * T) r :=
    h1.mul_const T
  have hmul : HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • S1) * T) * NormedSpace.exp ((-s) • S1))
      (((NormedSpace.exp (r • S1) * S1) * T) * NormedSpace.exp ((-r) • S1) +
        (NormedSpace.exp (r • S1) * T) * ((-S1) * NormedSpace.exp ((-r) • S1))) r :=
    h1T.mul h2'
  have hderiv_eq :
      ((NormedSpace.exp (r • S1) * S1) * T) * NormedSpace.exp ((-r) • S1) +
        (NormedSpace.exp (r • S1) * T) * ((-S1) * NormedSpace.exp ((-r) • S1)) =
        swAdjointFlow S1 r (adOp S1 T) := by
    simp only [swAdjointFlow, adOp]
    noncomm_ring
  simpa only [swAdjointFlow, hderiv_eq] using hmul

/-- Scaled adjoint flow derivative `d/du 𝒰_{u t}(T) = t • 𝒰_{u t}([S₁, T])`. -/
lemma hasDerivAt_swAdjointFlow_scaled (S1 T : A) (t u : ℝ) :
    HasDerivAt (fun s : ℝ => swAdjointFlow S1 (s * t) T)
      (t • swAdjointFlow S1 (u * t) (adOp S1 T)) u := by
  have hlin : HasDerivAt (fun s : ℝ => s * t) t u := by
    simpa using (hasDerivAt_id u).mul_const t
  have hcomp := (hasDerivAt_swAdjointFlow S1 T (u * t)).scomp u hlin
  simpa [Function.comp_def] using hcomp

lemma continuous_swAdjointFlow_scaled (S1 T : A) (t : ℝ) :
    Continuous (fun u : ℝ => swAdjointFlow S1 (u * t) T) :=
  continuous_iff_continuousAt.mpr fun u =>
    (hasDerivAt_swAdjointFlow_scaled S1 T t u).continuousAt

/-- Order-1 integral Taylor formula for the adjoint flow `𝒰_t(V)`:
`𝒰_t(V) = V + t [S₁, V] + t² ∫₀¹ (1 - u) 𝒰_{ut}(ad_{S₁}² V) du`. -/
theorem swAdjointFlow_taylor_order1 (S1 V : A) (t : ℝ) :
    swAdjointFlow S1 t V =
      V + t • adOp S1 V +
        (t ^ 2) • ∫ u in (0 : ℝ)..1, (1 - u) • swAdjointFlow S1 (u * t) (adIter S1 2 V) := by
  let g0 (u : ℝ) : A := swAdjointFlow S1 (u * t) V
  let g1 (u : ℝ) : A := swAdjointFlow S1 (u * t) (adOp S1 V)
  let g2 (u : ℝ) : A := swAdjointFlow S1 (u * t) (adIter S1 2 V)
  let Φ (u : ℝ) : A := g0 u + ((1 - u) * t) • g1 u
  have hΦ : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt Φ (((1 - u) * t ^ 2) • g2 u) u := by
    intro u _
    have hd0 : HasDerivAt g0 (t • g1 u) u := hasDerivAt_swAdjointFlow_scaled S1 V t u
    have hd1 : HasDerivAt g1 (t • g2 u) u := hasDerivAt_swAdjointFlow_scaled S1 (adOp S1 V) t u
    have hc : HasDerivAt (fun s : ℝ => (1 - s) * t) (-t) u := by
      simpa using (hasDerivAt_one_sub u).mul_const t
    have hterm : HasDerivAt (fun s : ℝ => ((1 - s) * t) • g1 s)
        (((1 - u) * t) • (t • g2 u) + (-t) • g1 u) u :=
      hc.smul hd1
    have hsum := hd0.add hterm
    have heq : t • g1 u + (((1 - u) * t) • (t • g2 u) + (-t) • g1 u) =
        ((1 - u) * t ^ 2) • g2 u := by
      rw [smul_smul, neg_smul]
      have hm : (1 - u) * t * t = (1 - u) * t ^ 2 := by ring
      rw [hm]
      abel
    rw [← heq]
    exact hsum
  have hint : IntervalIntegrable (fun u : ℝ => ((1 - u) * t ^ 2) • g2 u) MeasureTheory.volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ 0 1
    exact ((continuous_const.sub continuous_id).mul continuous_const).smul
      (continuous_swAdjointFlow_scaled S1 (adIter S1 2 V) t)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hΦ hint
  have hΦ1 : Φ 1 = swAdjointFlow S1 t V := by simp [Φ, g0, g1]
  have hΦ0 : Φ 0 = V + t • adOp S1 V := by simp [Φ, g0, g1]
  have hint_eq :
      (∫ u in (0 : ℝ)..1, ((1 - u) * t ^ 2) • g2 u) =
        (t ^ 2) • ∫ u in (0 : ℝ)..1, (1 - u) • g2 u := by
    have hrw : (fun u : ℝ => ((1 - u) * t ^ 2) • g2 u) =
        (fun u : ℝ => (t ^ 2) • ((1 - u) • g2 u)) := by
      funext u; rw [smul_smul, mul_comm]
    rw [hrw, intervalIntegral.integral_smul]
  rw [hΦ1, hΦ0, hint_eq] at hftc
  exact eq_add_of_sub_eq' hftc.symm

/-- Order-2 integral Taylor formula for the adjoint flow `𝒰_t(H₀)`:
`𝒰_t(H₀) = H₀ + t [S₁, H₀] + (t² / 2) ad_{S₁}² H₀ + (t³ / 2) ∫₀¹ (1 - u)² 𝒰_{ut}(ad_{S₁}³ H₀) du`. -/
theorem swAdjointFlow_taylor_order2 (S1 H0 : A) (t : ℝ) :
    swAdjointFlow S1 t H0 =
      H0 + t • adOp S1 H0 + (t ^ 2 / 2) • adIter S1 2 H0 +
        (t ^ 3 / 2) • ∫ u in (0 : ℝ)..1, ((1 - u) ^ 2) • swAdjointFlow S1 (u * t) (adIter S1 3 H0) := by
  let g0 (u : ℝ) : A := swAdjointFlow S1 (u * t) H0
  let g1 (u : ℝ) : A := swAdjointFlow S1 (u * t) (adOp S1 H0)
  let g2 (u : ℝ) : A := swAdjointFlow S1 (u * t) (adIter S1 2 H0)
  let g3 (u : ℝ) : A := swAdjointFlow S1 (u * t) (adIter S1 3 H0)
  let Φ (u : ℝ) : A :=
    g0 u + ((1 - u) * t) • g1 u + (((1 - u) ^ 2 / 2) * t ^ 2) • g2 u
  have hΦ : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt Φ (((t ^ 3 / 2) * (1 - u) ^ 2) • g3 u) u := by
    intro u _
    have hd0 : HasDerivAt g0 (t • g1 u) u := hasDerivAt_swAdjointFlow_scaled S1 H0 t u
    have hd1 : HasDerivAt g1 (t • g2 u) u := hasDerivAt_swAdjointFlow_scaled S1 (adOp S1 H0) t u
    have hd2 : HasDerivAt g2 (t • g3 u) u := hasDerivAt_swAdjointFlow_scaled S1 (adIter S1 2 H0) t u
    have h1u := hasDerivAt_one_sub u
    have hc1 : HasDerivAt (fun s : ℝ => (1 - s) * t) (-t) u := by
      simpa using h1u.mul_const t
    have hsq : HasDerivAt (fun s : ℝ => (1 - s) ^ 2) (-(2 * (1 - u))) u := by
      have hpow := h1u.pow 2
      convert hpow using 1
      ring
    have hc2 : HasDerivAt (fun s : ℝ => ((1 - s) ^ 2 / 2) * t ^ 2) (-((1 - u) * t ^ 2)) u := by
      have hd := (hsq.div_const 2).mul_const (t ^ 2)
      convert hd using 1
      ring
    have hterm1 : HasDerivAt (fun s : ℝ => ((1 - s) * t) • g1 s)
        (((1 - u) * t) • (t • g2 u) + (-t) • g1 u) u :=
      hc1.smul hd1
    have hterm2 : HasDerivAt (fun s : ℝ => (((1 - s) ^ 2 / 2) * t ^ 2) • g2 s)
        ((((1 - u) ^ 2 / 2) * t ^ 2) • (t • g3 u) + (-((1 - u) * t ^ 2)) • g2 u) u :=
      hc2.smul hd2
    have hsum := (hd0.add hterm1).add hterm2
    have heq :
        t • g1 u + (((1 - u) * t) • (t • g2 u) + (-t) • g1 u) +
          ((((1 - u) ^ 2 / 2) * t ^ 2) • (t • g3 u) + (-((1 - u) * t ^ 2)) • g2 u) =
          ((t ^ 3 / 2) * (1 - u) ^ 2) • g3 u := by
      rw [smul_smul, smul_smul, neg_smul, neg_smul]
      have hm1 : (1 - u) * t * t = (1 - u) * t ^ 2 := by ring
      have hm2 : (1 - u) ^ 2 / 2 * t ^ 2 * t = t ^ 3 / 2 * (1 - u) ^ 2 := by ring
      rw [hm1, hm2]
      abel
    rw [← heq]
    exact hsum
  have hint : IntervalIntegrable (fun u : ℝ => ((t ^ 3 / 2) * (1 - u) ^ 2) • g3 u)
      MeasureTheory.volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ 0 1
    exact (continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).smul
      (continuous_swAdjointFlow_scaled S1 (adIter S1 3 H0) t)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hΦ hint
  have hΦ1 : Φ 1 = swAdjointFlow S1 t H0 := by simp [Φ, g0, g1, g2]
  have hΦ0 : Φ 0 = H0 + t • adOp S1 H0 + (t ^ 2 / 2) • adIter S1 2 H0 := by
    simp [Φ, g0, g1, g2, div_eq_mul_inv, mul_comm]
  have hint_eq :
      (∫ u in (0 : ℝ)..1, ((t ^ 3 / 2) * (1 - u) ^ 2) • g3 u) =
        (t ^ 3 / 2) • ∫ u in (0 : ℝ)..1, ((1 - u) ^ 2) • g3 u := by
    have hrw : (fun u : ℝ => ((t ^ 3 / 2) * (1 - u) ^ 2) • g3 u) =
        (fun u : ℝ => (t ^ 3 / 2) • (((1 - u) ^ 2) • g3 u)) := by
      funext u; rw [smul_smul]
    rw [hrw, intervalIntegral.integral_smul]
  rw [hΦ1, hΦ0, hint_eq] at hftc
  exact eq_add_of_sub_eq' hftc.symm

/-- Equation `eq:ch21-sw-integral-remainder`: exact integral representation of the analytic
Schrieffer-Wolff Taylor remainder `R₃(t) = H̃(t) - B₂(t)`. -/
theorem swRemainder3_integral (H0 V S1 : A) (t : ℝ) :
    swRemainder3 H0 V S1 t =
      (t ^ 3 / 2) • (∫ u in (0 : ℝ)..1, ((1 - u) ^ 2) • swAdjointFlow S1 (u * t) (adIter S1 3 H0)) +
      (t ^ 3) • (∫ u in (0 : ℝ)..1, (1 - u) • swAdjointFlow S1 (u * t) (adIter S1 2 V)) := by
  let I3 : A := ∫ u in (0 : ℝ)..1, ((1 - u) ^ 2) • swAdjointFlow S1 (u * t) (adIter S1 3 H0)
  let I2 : A := ∫ u in (0 : ℝ)..1, (1 - u) • swAdjointFlow S1 (u * t) (adIter S1 2 V)
  have hH0 : swAdjointFlow S1 t H0 =
      H0 + t • adOp S1 H0 + (t ^ 2 / 2) • adIter S1 2 H0 + (t ^ 3 / 2) • I3 :=
    swAdjointFlow_taylor_order2 S1 H0 t
  have hV : swAdjointFlow S1 t V = V + t • adOp S1 V + (t ^ 2) • I2 :=
    swAdjointFlow_taylor_order1 S1 V t
  have ht2 : t * t = t ^ 2 := by ring
  have ht3 : t * t ^ 2 = t ^ 3 := by ring
  have hhalf : t ^ 2 / 2 = t ^ 2 * (2 : ℝ)⁻¹ := div_eq_mul_inv _ _
  calc
    swRemainder3 H0 V S1 t
      = swAdjointFlow S1 t H0 + t • swAdjointFlow S1 t V - swBchPoly2 H0 V S1 t := by
        unfold swRemainder3 swRotatedHam
        rw [swAdjointFlow_add, swAdjointFlow_smul]
    _ = (H0 + t • adOp S1 H0 + (t ^ 2 / 2) • adIter S1 2 H0 + (t ^ 3 / 2) • I3) +
          t • (V + t • adOp S1 V + (t ^ 2) • I2) -
          (H0 + t • (V + adOp S1 H0) + (t ^ 2) • (adOp S1 V + (2 : ℝ)⁻¹ • adIter S1 2 H0)) := by
        rw [hH0, hV]; rfl
    _ = (t ^ 3 / 2) • I3 + (t ^ 3) • I2 := by
        simp only [smul_add, smul_smul, ht2, ht3, hhalf]
        abel

/-- Euler trigonometric formula in any complete normed `ℝ`-algebra:
if `J * J = -1`, then `exp(t • J) = (cos t) • 1 + (sin t) • J` for all `t : ℝ`. -/
theorem exp_smul_of_sq_eq_neg_one {J : A} (hJ : J * J = -1) (t : ℝ) :
    NormedSpace.exp (t • J) = (Real.cos t) • (1 : A) + (Real.sin t) • J := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let R (s : ℝ) : A := (Real.cos s) • (1 : A) + (Real.sin s) • J
  let Ψ (s : ℝ) : A := NormedSpace.exp ((-s) • J) * R s
  have hR_deriv : ∀ s : ℝ, HasDerivAt R (J * R s) s := by
    intro s
    have hcos : HasDerivAt (fun u : ℝ => (Real.cos u) • (1 : A)) ((-Real.sin s) • (1 : A)) s :=
      (Real.hasDerivAt_cos s).smul_const (1 : A)
    have hsin : HasDerivAt (fun u : ℝ => (Real.sin u) • J) ((Real.cos s) • J) s :=
      (Real.hasDerivAt_sin s).smul_const J
    convert hcos.add hsin using 1
    dsimp only [R]
    rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one, hJ, smul_neg, neg_smul, add_comm]
  have hΨ_deriv : ∀ s : ℝ, HasDerivAt Ψ 0 s := by
    intro s
    have hexp : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-J)))
        (NormedSpace.exp (s • (-J)) * (-J)) s :=
      hasDerivAt_exp_smul_const (-J) s
    have hexp' : HasDerivAt (fun u : ℝ => NormedSpace.exp ((-u) • J))
        (NormedSpace.exp ((-s) • J) * (-J)) s := by
      have heq : (fun u : ℝ => NormedSpace.exp (u • (-J))) =
          (fun u : ℝ => NormedSpace.exp ((-u) • J)) := by
        funext u; rw [smul_neg, ← neg_smul]
      rw [heq, smul_neg, ← neg_smul] at hexp
      exact hexp
    have hmul := hexp'.mul (hR_deriv s)
    convert hmul using 1
    simp only [mul_neg, neg_mul, mul_assoc, neg_add_cancel]
  have hconst : Ψ t = Ψ 0 :=
    is_const_of_deriv_eq_zero (fun s => (hΨ_deriv s).differentiableAt)
      (fun s => (hΨ_deriv s).deriv) t 0
  have hΨ0 : Ψ 0 = 1 := by simp [Ψ, R]
  have hΨt : NormedSpace.exp ((-t) • J) * R t = 1 := hconst.trans hΨ0
  have hinv : NormedSpace.exp (t • J) * NormedSpace.exp ((-t) • J) = 1 := by
    rw [← NormedSpace.exp_add_of_commute
      (((Commute.refl J).smul_left t).smul_right (-t))]
    rw [← add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  calc
    NormedSpace.exp (t • J)
      = NormedSpace.exp (t • J) * (NormedSpace.exp ((-t) • J) * R t) := by rw [hΨt, mul_one]
    _ = (NormedSpace.exp (t • J) * NormedSpace.exp ((-t) • J)) * R t := by rw [mul_assoc]
    _ = R t := by rw [hinv, one_mul]

end AbstractAnalyticSWCalculus

section AbstractAnalyticSWCStar

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]

/-- Every orthogonal projection (`P² = P = P†`) in a `CStarRing` is a contraction `‖P‖ ≤ 1`. -/
lemma norm_ortho_proj_le_one {P : A} (hP : P * P = P) (hPstar : star P = P) :
    ‖P‖ ≤ 1 := by
  have hsq : ‖P‖ * ‖P‖ = ‖P‖ := by
    calc
      ‖P‖ * ‖P‖ = ‖star P * P‖ := (CStarRing.norm_star_mul_self (x := P)).symm
      _ = ‖P * P‖ := by rw [hPstar]
      _ = ‖P‖ := by rw [hP]
  have hfac : ‖P‖ * (‖P‖ - 1) = 0 := by linarith
  rcases mul_eq_zero.mp hfac with hz | h1
  · linarith
  · linarith

/-- Compression by an orthogonal projection contracts the operator norm: `‖P R P‖ ≤ ‖R‖`. -/
lemma norm_compress_le_of_ortho_proj {P : A} (hP : P * P = P) (hPstar : star P = P) (R : A) :
    ‖P * R * P‖ ≤ ‖R‖ := by
  have hle := norm_ortho_proj_le_one hP hPstar
  calc
    ‖P * R * P‖ ≤ ‖P * R‖ * ‖P‖ := norm_mul_le _ _
    _ ≤ (‖P‖ * ‖R‖) * ‖P‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ (1 * ‖R‖) * 1 := by
      gcongr
    _ = ‖R‖ := by ring

end AbstractAnalyticSWCStar

section AbstractAnalyticSWBounds

variable {A : Type*} [NormedRing A] [StarRing A] [CompleteSpace A] [CStarRing A]
  [NormedAlgebra ℝ A] [StarModule ℝ A]

/-- Exponential of a real multiple of a skew-adjoint generator is unitary. -/
lemma exp_smul_skew_mem_unitary {S1 : A} (hSkew : star S1 = -S1) (r : ℝ) :
    NormedSpace.exp (r • S1) ∈ unitary A := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff, star_smul, star_trivial, hSkew, smul_neg]

/-- Operator norm of a unitary exponential `‖exp(r S₁)‖ = 1` in any nontrivial `CStarRing`. -/
lemma norm_exp_smul_skew_eq_one [Nontrivial A] {S1 : A} (hSkew : star S1 = -S1) (r : ℝ) :
    ‖NormedSpace.exp (r • S1)‖ = 1 := by
  let U : unitary A := ⟨NormedSpace.exp (r • S1), exp_smul_skew_mem_unitary hSkew r⟩
  exact CStarRing.norm_coe_unitary U

/-- Unitary conjugation preserves the operator norm: `‖𝒰_r(T)‖ = ‖T‖` when `S₁† = -S₁`. -/
lemma swAdjointFlow_norm_eq {S1 : A} (hSkew : star S1 = -S1) (r : ℝ) (T : A) :
    ‖swAdjointFlow S1 r T‖ = ‖T‖ := by
  let U : unitary A := ⟨NormedSpace.exp (r • S1), exp_smul_skew_mem_unitary hSkew r⟩
  let V : unitary A := ⟨NormedSpace.exp ((-r) • S1), exp_smul_skew_mem_unitary hSkew (-r)⟩
  change ‖(U : A) * T * (V : A)‖ = ‖T‖
  rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

private lemma integral_one_sub_sq : ∫ u in (0 : ℝ)..1, (1 - u) ^ 2 = 1 / 3 := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => -((1 - s) ^ 3 / 3)) ((1 - u) ^ 2) u := by
    intro u _
    have h3 := ((hasDerivAt_one_sub u).pow 3).div_const 3 |>.neg
    convert h3 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (((continuous_const.sub continuous_id).pow 2).intervalIntegrable 0 1)]
  norm_num

private lemma integral_one_sub : ∫ u in (0 : ℝ)..1, (1 - u) = 1 / 2 := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => -((1 - s) ^ 2 / 2)) (1 - u) u := by
    intro u _
    have h2 := ((hasDerivAt_one_sub u).pow 2).div_const 2 |>.neg
    convert h2 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.sub continuous_id).intervalIntegrable 0 1)]
  norm_num

/-- Equation `eq:ch21-sw-norm-bound` (uncompressed): for skew-adjoint `S₁† = -S₁`,
`‖R₃(t)‖ ≤ |t|³ (‖ad_{S₁}³ H₀‖ / 6 + ‖ad_{S₁}² V‖ / 2)`. -/
theorem swRemainder3_norm_bound (H0 V : A) {S1 : A} (hSkew : star S1 = -S1) (t : ℝ) :
    ‖swRemainder3 H0 V S1 t‖ ≤
      |t| ^ 3 * (‖adIter S1 3 H0‖ / 6 + ‖adIter S1 2 V‖ / 2) := by
  rw [swRemainder3_integral H0 V S1 t]
  have hI1 : ‖∫ u in (0 : ℝ)..1, ((1 - u) ^ 2) • swAdjointFlow S1 (u * t) (adIter S1 3 H0)‖ ≤
      ‖adIter S1 3 H0‖ / 3 := by
    have hle : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
        ‖((1 - u) ^ 2) • swAdjointFlow S1 (u * t) (adIter S1 3 H0)‖ ≤
          (1 - u) ^ 2 * ‖adIter S1 3 H0‖ := by
      intro u _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), swAdjointFlow_norm_eq hSkew]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le
      (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 1)
      (Filter.Eventually.of_forall hle)
      ((((continuous_const.sub continuous_id).pow 2).mul continuous_const).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_mul_const, integral_one_sub_sq] at hbound
    linarith
  have hI2 : ‖∫ u in (0 : ℝ)..1, (1 - u) • swAdjointFlow S1 (u * t) (adIter S1 2 V)‖ ≤
      ‖adIter S1 2 V‖ / 2 := by
    have hle : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
        ‖(1 - u) • swAdjointFlow S1 (u * t) (adIter S1 2 V)‖ ≤
          (1 - u) * ‖adIter S1 2 V‖ := by
      intro u hu
      have hnn : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn, swAdjointFlow_norm_eq hSkew]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le
      (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 1)
      (Filter.Eventually.of_forall hle)
      (((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_mul_const, integral_one_sub] at hbound
    linarith
  have habs3 : |t ^ 3| = |t| ^ 3 := abs_pow t 3
  have hterm1 :
      ‖(t ^ 3 / 2) • ∫ u in (0 : ℝ)..1, ((1 - u) ^ 2) • swAdjointFlow S1 (u * t) (adIter S1 3 H0)‖ ≤
        |t| ^ 3 * (‖adIter S1 3 H0‖ / 6) := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, habs3, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hnn : 0 ≤ |t| ^ 3 / 2 := by positivity
    calc
      |t| ^ 3 / 2 * ‖∫ u in (0 : ℝ)..1, ((1 - u) ^ 2) • swAdjointFlow S1 (u * t) (adIter S1 3 H0)‖
        ≤ |t| ^ 3 / 2 * (‖adIter S1 3 H0‖ / 3) := mul_le_mul_of_nonneg_left hI1 hnn
      _ = |t| ^ 3 * (‖adIter S1 3 H0‖ / 6) := by ring
  have hterm2 :
      ‖(t ^ 3) • ∫ u in (0 : ℝ)..1, (1 - u) • swAdjointFlow S1 (u * t) (adIter S1 2 V)‖ ≤
        |t| ^ 3 * (‖adIter S1 2 V‖ / 2) := by
    rw [norm_smul, Real.norm_eq_abs, habs3]
    have hnn : 0 ≤ |t| ^ 3 := by positivity
    exact mul_le_mul_of_nonneg_left hI2 hnn
  calc
    ‖(t ^ 3 / 2) • (∫ u in (0 : ℝ)..1, ((1 - u) ^ 2) • swAdjointFlow S1 (u * t) (adIter S1 3 H0)) +
      (t ^ 3) • (∫ u in (0 : ℝ)..1, (1 - u) • swAdjointFlow S1 (u * t) (adIter S1 2 V))‖
      ≤ ‖(t ^ 3 / 2) • (∫ u in (0 : ℝ)..1, ((1 - u) ^ 2) • swAdjointFlow S1 (u * t) (adIter S1 3 H0))‖ +
        ‖(t ^ 3) • (∫ u in (0 : ℝ)..1, (1 - u) • swAdjointFlow S1 (u * t) (adIter S1 2 V))‖ :=
        norm_add_le _ _
    _ ≤ |t| ^ 3 * (‖adIter S1 3 H0‖ / 6) + |t| ^ 3 * (‖adIter S1 2 V‖ / 2) :=
        add_le_add hterm1 hterm2
    _ = |t| ^ 3 * (‖adIter S1 3 H0‖ / 6 + ‖adIter S1 2 V‖ / 2) := by ring

/-- Proposition `prop:ch21-sw-analytic-remainder` (`eq:ch21-sw-exact-plus-remainder`,
`eq:ch21-sw-integral-remainder`, `eq:ch21-sw-norm-bound`):
exact compressed rotated Hamiltonian plus remainder, integral remainder representation, and
operator-norm bound in any unital complex `CStarRing`. -/
theorem swCompressed_exact_plus_remainder_and_bound (P Q H0 V S1 : A) (t : ℝ)
    (hP : P * P = P) (hPstar : star P = P)
    (hPartition : P + Q = 1) (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (hSpp : P * S1 * P = 0) (hSkew : star S1 = -S1)
    (hGenerator : adOp S1 H0 = -(P * V * Q + Q * V * P)) :
    P * swRotatedHam H0 V S1 t * P =
      swEffPoly2 P H0 V S1 t + P * swRemainder3 H0 V S1 t * P ∧
    ‖P * swRemainder3 H0 V S1 t * P‖ ≤ ‖swRemainder3 H0 V S1 t‖ ∧
    ‖swRemainder3 H0 V S1 t‖ ≤
      |t| ^ 3 * (‖adIter S1 3 H0‖ / 6 + ‖adIter S1 2 V‖ / 2) := by
  have hbch := swBchPoly2_compressed P Q H0 V S1 t hP hPartition hPQ hQP hSpp hGenerator
  refine ⟨?_, norm_compress_le_of_ortho_proj hP hPstar _, swRemainder3_norm_bound H0 V hSkew t⟩
  unfold swRemainder3
  calc
    P * swRotatedHam H0 V S1 t * P
      = P * (swBchPoly2 H0 V S1 t + (swRotatedHam H0 V S1 t - swBchPoly2 H0 V S1 t)) * P := by
        simp
    _ = P * swBchPoly2 H0 V S1 t * P +
        P * (swRotatedHam H0 V S1 t - swBchPoly2 H0 V S1 t) * P := by
        simp only [mul_add, add_mul]
    _ = swEffPoly2 P H0 V S1 t +
        P * (swRotatedHam H0 V S1 t - swBchPoly2 H0 V S1 t) * P := by
        rw [hbch]

end AbstractAnalyticSWBounds

end Bosonize.Ch21
