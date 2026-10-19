import BosonizeStubs.V1S5FiniteGroundState
import Bosonize.Core.V1S1OrderedWick

/-! S5 staging: the complete zero-charge K=2 partition budget, h=8, M=2. -/
@[expose] public section
namespace Bosonize.V1S5
open scoped BigOperators
open Matrix

def smallCharges : Fin 2 → ℤ := fun _ => 0
def smallBranches : A06.Branches (Fin 2) := Ch18.concreteBranches

theorem small_admissible : A05.admissible 8 smallCharges := by
  intro ν
  norm_num [smallCharges, Ch07.admissible]

/-- Order: vacuum, R1, L1, R11, L11, R1L1, R2, L2. -/
def smallParts (j : Fin 8) : Fin 2 → List ℕ :=
  ![![[], []], ![[1], []], ![[], [1]], ![[1, 1], []],
    ![[], [1, 1]], ![[1], [1]], ![[2], []], ![[], [2]]] j

noncomputable def smallCoefficient (j : Fin 8) : ℂ :=
  if j = 3 ∨ j = 4 ∨ j = 6 ∨ j = 7 then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 1

noncomputable def smallVector (j : Fin 8) : Budget 8 smallCharges 2 :=
  ⟨smallCoefficient j • A05.wordState 8 smallCharges (smallParts j), by
    apply Submodule.smul_mem
    apply A05.word_mem_budget 8 (by norm_num) smallCharges small_admissible
    fin_cases j <;> norm_num [smallParts, Fin.sum_univ_two]⟩

noncomputable def smallHamiltonian : Module.End ℂ (Budget 8 smallCharges 2) :=
  budgetHamiltonian 8 2 2 smallCharges 1 (32 * Real.pi) (30 * Real.pi)
    (Ch17.canonicalMu 8 1) smallBranches

noncomputable def smallMatrix : Matrix (Fin 8) (Fin 8) ℂ := fun i j =>
  ((Real.pi / 8 : ℝ) : ℂ) *
    if (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) then 15
    else if i = j then if i = 0 then 0 else if i = 1 ∨ i = 2 then 17 else 34
    else 0

noncomputable def smallEta : ℝ := 15 / (17 + Real.sqrt 514)
noncomputable def smallEnergy : ℝ := Real.pi / 8 * (17 - Real.sqrt 514)
noncomputable def smallEigenvalue (j : Fin 8) : ℝ :=
  if j = 0 then smallEnergy
  else if j = 5 then Real.pi / 8 * (17 + Real.sqrt 514)
  else if j = 1 ∨ j = 2 then 17 * (Real.pi / 8) else 34 * (Real.pi / 8)
noncomputable def smallPsi : Budget 8 smallCharges 2 :=
  (((Real.sqrt (1 + smallEta ^ 2))⁻¹ : ℝ) : ℂ) •
    (smallVector 0 - (smallEta : ℂ) • smallVector 5)

theorem small_orthonormal : Orthonormal ℂ smallVector := by sorry

theorem small_complete : Submodule.span ℂ (Set.range smallVector) = ⊤ := by sorry

/-- Complete operator action, including all six complementary eigenvectors. -/
theorem small_matrix_action (j : Fin 8) :
    smallHamiltonian (smallVector j) = ∑ i : Fin 8, smallMatrix i j • smallVector i := by sorry

/-- All eight eigenvalues with multiplicity, on a complete orthonormal basis. -/
theorem small_spectral_basis :
    ∃ b : OrthonormalBasis (Fin 8) ℂ (Budget 8 smallCharges 2),
      ∀ j, smallHamiltonian (b j) = (smallEigenvalue j : ℂ) • b j := by sorry

theorem small_ground : ‖smallPsi‖ = 1 ∧
    smallHamiltonian smallPsi = (smallEnergy : ℂ) • smallPsi ∧
    (∀ v : Budget 8 smallCharges 2,
      smallEnergy * ‖v‖ ^ 2 ≤ (inner ℂ v (smallHamiltonian v)).re) ∧ smallEnergy < 0 := by sorry

theorem small_number_moment :
    extendedState (E := Budget 8 smallCharges 2) (inclusion 8 smallCharges 2) smallPsi
      (A05.rho 8 (smallBranches.rightSpecies) 1 *
        A05.rho 8 (smallBranches.rightSpecies) (-1)) =
      (((1 - 17 / Real.sqrt 514) / 2 : ℝ) : ℂ) := by sorry

theorem small_pair_moment :
    extendedState (E := Budget 8 smallCharges 2) (inclusion 8 smallCharges 2) smallPsi
      (A05.rho 8 (smallBranches.rightSpecies) 1 *
        A05.rho 8 (smallBranches.leftSpecies) 1) =
      ((-15 / (2 * Real.sqrt 514) : ℝ) : ℂ) := by sorry

theorem small_number_discrepancy :
    extendedState (E := Budget 8 smallCharges 2) (inclusion 8 smallCharges 2) smallPsi
      (A05.rho 8 smallBranches.rightSpecies 1 * A05.rho 8 smallBranches.rightSpecies (-1)) ≠
      A08.omegaP 2 Ch18.concretePair
        (A08.creatorGen 2 .right 0 * A08.annihilatorGen 2 .right 0) := by sorry

theorem small_pair_discrepancy :
    extendedState (E := Budget 8 smallCharges 2) (inclusion 8 smallCharges 2) smallPsi
      (A05.rho 8 smallBranches.rightSpecies 1 * A05.rho 8 smallBranches.leftSpecies 1) ≠
      A08.omegaP 2 Ch18.concretePair
        (A08.creatorGen 2 .right 0 * A08.creatorGen 2 .left 0) := by sorry

end Bosonize.V1S5
