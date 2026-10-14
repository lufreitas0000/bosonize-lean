import Bosonize
import BosonizeStubs.A07InteractionsAndBogoliubov

namespace Bosonize.A10

open scoped BigOperators Classical

section MatrixModels

noncomputable def swGeneratorMatrix {ι : Type*}
    (inLow : ι → Bool) (E : ι → ℝ) (Voff : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  fun i j =>
    if inLow i ≠ inLow j ∧ Voff i j ≠ 0 then
      Voff i j / ((E i - E j : ℝ) : ℂ)
    else 0

noncomputable def diagEnergyMatrix {ι : Type*} [DecidableEq ι]
    (E : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => ((E i : ℝ) : ℂ))

def nonResonant {ι : Type*} (inLow : ι → Bool) (E : ι → ℝ)
    (Voff : Matrix ι ι ℂ) : Prop :=
  ∀ i j : ι, inLow i ≠ inLow j → Voff i j ≠ 0 → E i ≠ E j

def swCounterH0_2x2 : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 1 ∧ j = 1 then 1 else 0

def swCounterV_2x2 : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i ≠ j then 1 else 0

def swCounterS1_2x2 : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 1 then -1 else if i = 1 ∧ j = 0 then 1 else 0

def swCounterP_2x2 : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

def swCounterH0_3x3 : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    if i = j then
      if i = 0 then 0 else if i = 1 then -1 else 1
    else 0

def swCounterP_3x3 : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

def swCounterQ_3x3 : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => if i = j ∧ (i = 1 ∨ i = 2) then 1 else 0

def swCounterV_3x3 : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    if (i = 0 ∧ (j = 1 ∨ j = 2)) ∨ ((i = 1 ∨ i = 2) ∧ j = 0) then 1
    else 0

def swCounterS1_3x3 : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    if i = 0 ∧ j = 1 then 1
    else if i = 0 ∧ j = 2 then -1
    else if i = 1 ∧ j = 0 then -1
    else if i = 2 ∧ j = 0 then 1
    else 0

theorem sw_generator_commutator_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (inLow : ι → Bool) (E : ι → ℝ) (Voff : Matrix ι ι ℂ)
    (hBlock : ∀ i j : ι, inLow i = inLow j → Voff i j = 0)
    (hNonRes : nonResonant inLow E Voff) :
    swGeneratorMatrix inLow E Voff * diagEnergyMatrix E -
      diagEnergyMatrix E * swGeneratorMatrix inLow E Voff = -Voff := by sorry

theorem sw_generator_skew_hermitian {ι : Type*}
    (inLow : ι → Bool) (E : ι → ℝ) (Voff : Matrix ι ι ℂ)
    (hHerm : Matrix.conjTranspose Voff = Voff) :
    Matrix.conjTranspose (swGeneratorMatrix inLow E Voff) =
      -swGeneratorMatrix inLow E Voff := by sorry

theorem sw_2x2_truncation_witness :
    swCounterS1_2x2 * swCounterH0_2x2 - swCounterH0_2x2 * swCounterS1_2x2 =
      -swCounterV_2x2 ∧
    (swCounterP_2x2 * (swCounterS1_2x2 * swCounterV_2x2 -
      swCounterV_2x2 * swCounterS1_2x2) * swCounterP_2x2) 0 0 = -2 ∧
    ((-((2 : ℚ) / 3) ^ 2 : ℚ) ≠ (-1 / 3 : ℚ)) := by sorry

theorem sw_3x3_no_iff_witness :
    swCounterS1_3x3 * swCounterH0_3x3 - swCounterH0_3x3 * swCounterS1_3x3 =
      -swCounterV_3x3 ∧
    swCounterP_3x3 * swCounterV_3x3 * swCounterQ_3x3 ≠ 0 ∧
    swCounterP_3x3 * (swCounterS1_3x3 * swCounterV_3x3 -
      swCounterV_3x3 * swCounterS1_3x3) * swCounterP_3x3 = 0 := by sorry

def swCounterEigenvector_2x2 : Fin 2 → ℂ :=
  fun i => if i = 0 then -2 else 1

theorem sw_2x2_exact_eigenpair :
    swCounterEigenvector_2x2 ≠ 0 ∧
      (swCounterH0_2x2 + ((2 : ℂ) / 3) • swCounterV_2x2).mulVec
        swCounterEigenvector_2x2 =
      ((-1 : ℂ) / 3) • swCounterEigenvector_2x2 := by sorry

end MatrixModels

section BudgetShells

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

def exactShellSet (h : ℕ) (Ns : σ → ℤ) (K : ℕ) :
    Set (A05.Occupation σ h) :=
  {S | (∀ ν, Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) = Ns ν) ∧
    Ch07.totalExcitation h S = (K : ℤ)}

noncomputable def lowShellProj (h : ℕ) (Ns : σ → ℤ) (K : ℕ) :
    A05.Operators σ h :=
  Ch14.projection h Ns (K - 1)

noncomputable def highShellProj (h : ℕ) (Ns : σ → ℤ) (K : ℕ) :
    A05.Operators σ h :=
  letI : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq
  A03.coordinateProjection (exactShellSet h Ns K)

noncomputable def doubleModeOneKet (h : ℕ) (Ns : σ → ℤ) (ν : σ) :
    A05.FockSpace σ h :=
  A05.rho h ν 1 (A05.rho h ν 1 (A05.groundKet h Ns))

noncomputable def diagPart (h : ℕ) (P Q V : A05.Operators σ h) :
    A05.Operators σ h :=
  P * V * P + Q * V * Q

noncomputable def offDiagPart (h : ℕ) (P Q V : A05.Operators σ h) :
    A05.Operators σ h :=
  P * V * Q + Q * V * P

noncomputable def swSecondOrderCorrection (h : ℕ)
    (P S1 V : A05.Operators σ h) : A05.Operators σ h :=
  ((2 : ℂ)⁻¹) • (P * A02.commutator S1 V * P)

noncomputable def swEffectiveSecondOrder (h : ℕ)
    (P H0 V S1 : A05.Operators σ h) (t : ℝ) : A05.Operators σ h :=
  P * H0 * P + (t : ℂ) • (P * V * P) +
    ((t : ℂ) ^ 2) • swSecondOrderCorrection h P S1 V

noncomputable def bchSecondOrderPolynomial (h : ℕ)
    (H0 V S1 : A05.Operators σ h) (t : ℝ) : A05.Operators σ h :=
  H0 + (t : ℂ) • (V + A02.commutator S1 H0) +
    ((t : ℂ) ^ 2) • (A02.commutator S1 V +
      ((2 : ℂ)⁻¹) • A02.commutator S1 (A02.commutator S1 H0))

theorem sw_compressed_bch_second_order (h : ℕ)
    (P Q H0 V S1 : A05.Operators σ h) (t : ℝ)
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPartition : P + Q = 1) (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (hBaseline : A02.commutator P H0 = 0)
    (hSpp : P * S1 * P = 0) (hSqq : Q * S1 * Q = 0)
    (hGenerator : A02.commutator S1 H0 = -offDiagPart h P Q V) :
    P * bchSecondOrderPolynomial h H0 V S1 t * P =
      swEffectiveSecondOrder h P H0 V S1 t := by sorry

lemma shell_proj_partition (h K : ℕ) (hK : 1 ≤ K) (Ns : σ → ℤ) :
    lowShellProj h Ns K + highShellProj h Ns K =
      Ch14.projection h Ns K := by sorry

lemma shell_proj_orthogonal (h K : ℕ) (hK : 1 ≤ K) (Ns : σ → ℤ) :
    lowShellProj h Ns K * highShellProj h Ns K = 0 ∧
      highShellProj h Ns K * lowShellProj h Ns K = 0 := by sorry

lemma shell_proj_self_adjoint (h K : ℕ) (Ns : σ → ℤ) :
    LinearMap.adjoint (lowShellProj h Ns K) = lowShellProj h Ns K ∧
      LinearMap.adjoint (highShellProj h Ns K) = highShellProj h Ns K := by sorry

lemma energy_shell_discards_double_mode_one (h : ℕ) (hh : 2 ≤ h)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns) (ν : σ)
    (hR2 : A05.r2 h 2 Ns) :
    doubleModeOneKet h Ns ν ∈ A05.jointBudget h Ns 2 ∧
      doubleModeOneKet h Ns ν ≠ 0 ∧
      lowShellProj h Ns 2 (doubleModeOneKet h Ns ν) = 0 ∧
      highShellProj h Ns 2 (doubleModeOneKet h Ns ν) =
        doubleModeOneKet h Ns ν := by sorry

theorem sw_off_zero_implies_effective_exact (h : ℕ)
    (P Q H0 V : A05.Operators σ h) (t : ℝ)
    (hPVQ : P * V * Q = 0) (hQVP : Q * V * P = 0) :
    offDiagPart h P Q V = 0 ∧
      swSecondOrderCorrection h P (0 : A05.Operators σ h) V = 0 ∧
      swEffectiveSecondOrder h P H0 V (0 : A05.Operators σ h) t =
        P * H0 * P + (t : ℂ) • (P * V * P) := by sorry

end BudgetShells

end Bosonize.A10
