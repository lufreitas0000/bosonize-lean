import Bosonize.Core.A07FiniteNormalOrdering
import Bosonize.Core.Ch16FieldHamiltonian
import Bosonize.Core.A06ChiralFields
import Bosonize.Core.Ch15DualFields
import Bosonize.Core.Ch01LatticeBand
import Bosonize.Core.Ch02UmbralCalculus
import Bosonize.Core.A01FourierCharacters
import Bosonize.Core.Ch03Fourier
import Bosonize.Core.A02CARHilbert
import Bosonize.Core.Ch04CARFock
import Bosonize.Core.Ch05Fermions
import Bosonize.Core.Ch06LocalNet
import Bosonize.Core.Ch06Ext
import Bosonize.Core.A03EnergyBudgets
import Bosonize.Core.Ch07VacuumBudget
import Bosonize.Core.Ch08Boson
import Bosonize.Core.A05MultiSpecies
import Bosonize.Core.Ch13KleinFactors
import Bosonize.Core.A05FiniteExponentials
import Bosonize.Core.Ch14Mandelstam
import Bosonize.Core.A04DensityKinematics
import Bosonize.Core.Ch09DensityModes
import Bosonize.Core.A04CurrentMargins
import Bosonize.Core.Ch10Heisenberg
import Bosonize.Core.A04PartitionCombinatorics
import Bosonize.Core.Ch11HaldaneCompleteness
import Bosonize.Core.Ch12Sugawara
import Bosonize.Core.A07InteractionsAndBogoliubov

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
      diagEnergyMatrix E * swGeneratorMatrix inLow E Voff = -Voff := by
  ext i j
  simp only [Matrix.sub_apply, diagEnergyMatrix, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.neg_apply]
  by_cases hb : inLow i = inLow j
  · simp [swGeneratorMatrix, hb, hBlock i j hb]
  by_cases hv : Voff i j = 0
  · simp [swGeneratorMatrix, hv]
  have he : E i ≠ E j := hNonRes i j hb hv
  have hd : ((E i - E j : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr he
  change (if inLow i ≠ inLow j ∧ Voff i j ≠ 0 then
    Voff i j / ((E i - E j : ℝ) : ℂ) else 0) * (E j : ℂ) -
    (E i : ℂ) * (if inLow i ≠ inLow j ∧ Voff i j ≠ 0 then
    Voff i j / ((E i - E j : ℝ) : ℂ) else 0) = -Voff i j
  rw [ite_eq_left ⟨hb, hv⟩]
  push_cast at hd ⊢
  field_simp
  ring

theorem sw_generator_skew_hermitian {ι : Type*}
    (inLow : ι → Bool) (E : ι → ℝ) (Voff : Matrix ι ι ℂ)
    (hHerm : Matrix.conjTranspose Voff = Voff) :
    Matrix.conjTranspose (swGeneratorMatrix inLow E Voff) =
      -swGeneratorMatrix inLow E Voff := by
  ext i j
  have hs : star (Voff j i) = Voff i j := congrFun (congrFun hHerm i) j
  have ht : Voff j i = star (Voff i j) := by
    simpa only [star_star] using congrArg star hs
  change star (swGeneratorMatrix inLow E Voff j i) =
    -swGeneratorMatrix inLow E Voff i j
  by_cases hb : inLow i = inLow j
  · simp [swGeneratorMatrix, hb]
  by_cases hv : Voff i j = 0
  · simp [swGeneratorMatrix, ht, hv]
  have hvji : Voff j i ≠ 0 := by simp [ht, hv]
  rw [swGeneratorMatrix, swGeneratorMatrix,
    ite_eq_left ⟨Ne.symm hb, hvji⟩, ite_eq_left ⟨hb, hv⟩]
  have he : E j - E i = -(E i - E j) := by ring
  rw [he]
  simp only [star_div₀, hs, Complex.ofReal_neg, star_neg, Complex.star_def, Complex.conj_ofReal, div_neg]

theorem sw_2x2_truncation_witness :
    swCounterS1_2x2 * swCounterH0_2x2 - swCounterH0_2x2 * swCounterS1_2x2 =
      -swCounterV_2x2 ∧
    (swCounterP_2x2 * (swCounterS1_2x2 * swCounterV_2x2 -
      swCounterV_2x2 * swCounterS1_2x2) * swCounterP_2x2) 0 0 = -2 ∧
    ((-((2 : ℚ) / 3) ^ 2 : ℚ) ≠ (-1 / 3 : ℚ)) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, swCounterS1_2x2,
        swCounterH0_2x2, swCounterV_2x2]
  constructor
  · norm_num [Matrix.mul_apply, Fin.sum_univ_two, swCounterS1_2x2,
      swCounterH0_2x2, swCounterV_2x2, swCounterP_2x2]
  · norm_num

theorem sw_3x3_no_iff_witness :
    swCounterS1_3x3 * swCounterH0_3x3 - swCounterH0_3x3 * swCounterS1_3x3 =
      -swCounterV_3x3 ∧
    swCounterP_3x3 * swCounterV_3x3 * swCounterQ_3x3 ≠ 0 ∧
    swCounterP_3x3 * (swCounterS1_3x3 * swCounterV_3x3 -
      swCounterV_3x3 * swCounterS1_3x3) * swCounterP_3x3 = 0 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ, swCounterS1_3x3,
        swCounterH0_3x3, swCounterV_3x3]
  constructor
  · intro he
    have he01 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 0 1) he
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, swCounterP_3x3,
      swCounterV_3x3, swCounterQ_3x3] at he01
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ, swCounterS1_3x3,
        swCounterV_3x3, swCounterP_3x3]

def swCounterEigenvector_2x2 : Fin 2 → ℂ :=
  fun i => if i = 0 then -2 else 1

theorem sw_2x2_exact_eigenpair :
    swCounterEigenvector_2x2 ≠ 0 ∧
      (swCounterH0_2x2 + ((2 : ℂ) / 3) • swCounterV_2x2).mulVec
        swCounterEigenvector_2x2 =
      ((-1 : ℂ) / 3) • swCounterEigenvector_2x2 := by
  constructor
  · intro he
    have he0 := congrFun he 0
    norm_num [swCounterEigenvector_2x2] at he0
  · funext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        swCounterEigenvector_2x2, swCounterH0_2x2, swCounterV_2x2]

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
      swEffectiveSecondOrder h P H0 V S1 t := by
  have _ := hQ
  have _ := hBaseline
  have _ := hSqq
  have hl : P * S1 * Q = P * S1 := by
    calc
      P * S1 * Q = P * S1 * P + P * S1 * Q := by rw [hSpp]; simp
      _ = P * S1 * (P + Q) := by rw [mul_add]
      _ = P * S1 := by rw [hPartition]; simp
  have hr : Q * S1 * P = S1 * P := by
    calc
      Q * S1 * P = P * S1 * P + Q * S1 * P := by rw [hSpp]; simp
      _ = (P + Q) * S1 * P := by rw [add_mul, add_mul]
      _ = S1 * P := by rw [hPartition]; simp
  have hor : offDiagPart h P Q V * P = Q * V * P := by
    unfold offDiagPart
    rw [add_mul]
    have hz : P * V * Q * P = 0 := by
      calc
        P * V * Q * P = P * V * (Q * P) := by simp only [mul_assoc]
        _ = 0 := by rw [hQP]; simp
    rw [hz]
    have hp : Q * V * P * P = Q * V * P := by rw [mul_assoc, hP]
    rw [hp]; simp
  have hol : P * offDiagPart h P Q V = P * V * Q := by
    unfold offDiagPart
    rw [mul_add]
    have hfirst : P * (P * V * Q) = P * V * Q := by simp only [← mul_assoc, hP]
    have hsecond : P * (Q * V * P) = 0 := by simp only [← mul_assoc, hPQ, zero_mul]
    rw [hfirst, hsecond]; simp
  have hoz : P * offDiagPart h P Q V * P = 0 := by
    rw [hol]
    calc
      P * V * Q * P = P * V * (Q * P) := by simp only [mul_assoc]
      _ = 0 := by rw [hQP]; simp
  have hleft : P * S1 * offDiagPart h P Q V * P = P * S1 * V * P := by
    calc
      P * S1 * offDiagPart h P Q V * P = P * S1 * (offDiagPart h P Q V * P) := by simp only [mul_assoc]
      _ = P * S1 * (Q * V * P) := by rw [hor]
      _ = (P * S1 * Q) * V * P := by simp only [mul_assoc]
      _ = P * S1 * V * P := by rw [hl]
  have hright : P * offDiagPart h P Q V * S1 * P = P * V * S1 * P := by
    rw [hol]
    calc
      P * V * Q * S1 * P = P * V * (Q * S1 * P) := by simp only [mul_assoc]
      _ = P * V * (S1 * P) := by rw [hr]
      _ = P * V * S1 * P := by simp only [mul_assoc]
  have hc : P * A02.commutator S1 (offDiagPart h P Q V) * P =
      P * A02.commutator S1 V * P := by
    simp only [A02.commutator, mul_sub, sub_mul, ← mul_assoc, hleft, hright]
  have hn : A02.commutator S1 (-offDiagPart h P Q V) =
      -A02.commutator S1 (offDiagPart h P Q V) := by
    simp only [A02.commutator, mul_neg, neg_mul, neg_sub]
    abel
  have hlin : P * (V + A02.commutator S1 H0) * P = P * V * P := by
    rw [hGenerator]
    simp only [mul_add, add_mul, mul_neg, neg_mul, hoz, neg_zero, add_zero]
  have hquad : P * (A02.commutator S1 V + ((2 : ℂ)⁻¹) •
      A02.commutator S1 (A02.commutator S1 H0)) * P =
      ((2 : ℂ)⁻¹) • (P * A02.commutator S1 V * P) := by
    rw [hGenerator, hn]
    simp only [mul_add, add_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      mul_neg, neg_mul, hc]
    module
  have hdist (A B C : A05.Operators σ h) (a b : ℂ) :
      P * (A + a • B + b • C) * P =
        P * A * P + a • (P * B * P) + b • (P * C * P) := by
    simp only [mul_add, add_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  unfold bchSecondOrderPolynomial
  rw [hdist, hlin, hquad]
  rfl

lemma shell_proj_partition (h K : ℕ) (hK : 1 ≤ K) (Ns : σ → ℤ) :
    lowShellProj h Ns K + highShellProj h Ns K =
      Ch14.projection h Ns K := by
  let : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq
  apply A02.end_ext_basis
  intro S
  simp only [lowShellProj, highShellProj, Ch14.projection, LinearMap.add_apply,
    A03.projection_ket, Ch14.budgetSet, exactShellSet, Set.mem_ofPred_eq]
  have hn : ((K - 1 : ℕ) : ℤ) = (K : ℤ) - 1 := by omega
  by_cases hc : ∀ ν, Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) = Ns ν
  · by_cases he : Ch07.totalExcitation h S ≤ ((K - 1 : ℕ) : ℤ)
    · have ht : Ch07.totalExcitation h S ≤ (K : ℤ) := by omega
      have hne : Ch07.totalExcitation h S ≠ (K : ℤ) := by omega
      simp [hc, he, ht, hne]
    · by_cases ht : Ch07.totalExcitation h S ≤ (K : ℤ)
      · have heq : Ch07.totalExcitation h S = (K : ℤ) := by omega
        have hk : ¬ K ≤ K - 1 := by omega
        simp [hc, heq, hk]
      · have hne : Ch07.totalExcitation h S ≠ (K : ℤ) := by omega
        simp [hc, he, ht, hne]
  · simp [hc]

lemma shell_proj_orthogonal (h K : ℕ) (hK : 1 ≤ K) (Ns : σ → ℤ) :
    lowShellProj h Ns K * highShellProj h Ns K = 0 ∧
      highShellProj h Ns K * lowShellProj h Ns K = 0 := by
  let : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq
  have hz : lowShellProj h Ns K * highShellProj h Ns K = 0 := by
    rw [lowShellProj, highShellProj, Ch14.projection, A03.projection_intersection]
    have he : Ch14.budgetSet h Ns (K - 1) ∩ exactShellSet h Ns K = ∅ := by
      ext S
      simp only [Set.mem_inter_iff, Ch14.budgetSet, exactShellSet,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, hs⟩, ⟨_, he⟩⟩
      rw [he] at hs
      have hn : ((K - 1 : ℕ) : ℤ) = (K : ℤ) - 1 := by omega
      rw [hn] at hs
      omega
    rw [he]
    apply A02.end_ext_basis
    intro S
    simp [A03.projection_ket]
  refine ⟨hz, ?_⟩
  rw [lowShellProj, highShellProj, Ch14.projection, A03.projection_commute]
  exact hz

lemma shell_proj_self_adjoint (h K : ℕ) (Ns : σ → ℤ) :
    LinearMap.adjoint (lowShellProj h Ns K) = lowShellProj h Ns K ∧
      LinearMap.adjoint (highShellProj h Ns K) = highShellProj h Ns K := by
  let : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq
  simp only [lowShellProj, highShellProj, Ch14.projection, A03.projection_adjoint,
    and_self]

lemma energy_shell_discards_double_mode_one (h : ℕ) (hh : 2 ≤ h)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns) (ν : σ)
    (hR2 : A05.r2 h 2 Ns) :
    doubleModeOneKet h Ns ν ∈ A05.jointBudget h Ns 2 ∧
      doubleModeOneKet h Ns ν ≠ 0 ∧
      lowShellProj h Ns 2 (doubleModeOneKet h Ns ν) = 0 ∧
      highShellProj h Ns 2 (doubleModeOneKet h Ns ν) =
        doubleModeOneKet h Ns ν := by
  have hh0 : 0 < h := by omega
  let g := A05.groundKet h Ns
  let A := A05.rho h ν (-1)
  let C := A05.rho h ν 1
  let w := doubleModeOneKet h Ns ν
  let P := lowShellProj h Ns 2
  have hg : g ∈ A05.jointBudget h Ns 0 := A05.ground_mem_budget h hh0 Ns hN 0
  have hc : C g ∈ A05.jointBudget h Ns 1 := by
    simpa [C, A05.jointBudget] using A05.rho_budget_map h ν 1 Ns 0 g hg
  have hw : w ∈ A05.jointBudget h Ns 2 := by
    simpa [w, doubleModeOneKet, C, A05.jointBudget] using
      A05.rho_budget_map h ν 1 Ns 1 (C g) hc
  have hAg : A g = 0 :=
    A05.rho_lowering_budget_zero h hh0 ν 1 0 (by omega) Ns g hg
  have hCCR (J : ℕ) (hJ : J ≤ 1) (v : A05.FockSpace σ h)
      (hv : v ∈ A05.jointBudget h Ns J) : A (C v) = C (A v) + v := by
    have he := A06.joint_signed_current_commutator h J hh0 Ns ν (-1) 1
      (by have hr := hR2 ν; norm_num; omega) v hv
    norm_num [A02.commutator, Ch10.schwingerCoefficient, Module.End.mul_apply] at he
    change A (C v) - C (A v) = v at he
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  have hACg : A (C g) = g := by rw [hCCR 0 (by omega) g hg, hAg, map_zero, zero_add]
  have hAw : A w = (2 : ℂ) • C g := by
    change A (C (C g)) = _
    rw [hCCR 1 le_rfl (C g) hc, hACg]
    module
  have hAAw : A (A w) = (2 : ℂ) • g := by rw [hAw, map_smul, hACg]
  have hn : w ≠ 0 := by
    intro hz
    rw [hz, map_zero, map_zero] at hAAw
    have hhg := (smul_eq_zero.mp hAAw.symm).resolve_left (by norm_num)
    exact A05.ground_ne_zero h Ns hhg
  let : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
  let : LT (A05.Mode σ h) := (A05.speciesOrder h).toLT
  let : LE (A05.Mode σ h) := (A05.speciesOrder h).toLE
  let : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq
  have hpv : P w ∈ A05.jointBudget h Ns 1 := by
    change P w ∈ A03.coordinateSpace (Ch14.budgetSet h Ns 1)
    rw [← A03.projection_range]
    exact ⟨w, rfl⟩
  have hap : A (P w) ∈ A05.jointBudget h Ns 0 := by
    simpa [A, A05.jointBudget] using A05.rho_budget_map h ν (-1) Ns 1 (P w) hpv
  have haap : A (A (P w)) = 0 :=
    A05.rho_lowering_budget_zero h hh0 ν 1 0 (by omega) Ns (A (P w)) hap
  have hadj : LinearMap.adjoint A = C := by
    simpa [A, C] using A05.rho_adjoint h ν (-1)
  have hi : inner ℂ w (P w) = inner ℂ g (A (A (P w))) := by
    change inner ℂ (C (C g)) (P w) = _
    rw [← hadj, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
  have hpAdj : LinearMap.adjoint P = P := (shell_proj_self_adjoint h 2 Ns).1
  have hpId : P * P = P := by
    simp only [P, lowShellProj, Ch14.projection, A03.projection_idempotent]
  have hpp : P (P w) = P w := congrArg (fun B : A05.Operators σ h => B w) hpId
  have hlow : P w = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    calc
      inner ℂ (P w) (P w) = inner ℂ (LinearMap.adjoint P w) (P w) := by rw [hpAdj]
      _ = inner ℂ w (P (P w)) := LinearMap.adjoint_inner_left P (P w) w
      _ = inner ℂ w (P w) := by rw [hpp]
      _ = 0 := by rw [hi, haap]; simp
  refine ⟨hw, hn, hlow, ?_⟩
  have hpart := congrArg (fun B : A05.Operators σ h => B w)
    (shell_proj_partition h 2 (by omega) Ns)
  have hfix : Ch14.projection h Ns 2 w = w := by
    rw [Ch14.projection]
    apply (A03.projection_fixed_iff _ _).mpr
    exact hw
  rw [LinearMap.add_apply, hlow, zero_add, hfix] at hpart
  exact hpart

theorem sw_off_zero_implies_effective_exact (h : ℕ)
    (P Q H0 V : A05.Operators σ h) (t : ℝ)
    (hPVQ : P * V * Q = 0) (hQVP : Q * V * P = 0) :
    offDiagPart h P Q V = 0 ∧
      swSecondOrderCorrection h P (0 : A05.Operators σ h) V = 0 ∧
      swEffectiveSecondOrder h P H0 V (0 : A05.Operators σ h) t =
        P * H0 * P + (t : ℂ) • (P * V * P) := by
  simp [offDiagPart, hPVQ, hQVP, swSecondOrderCorrection,
    swEffectiveSecondOrder, A02.commutator]

end BudgetShells

end Bosonize.A10
