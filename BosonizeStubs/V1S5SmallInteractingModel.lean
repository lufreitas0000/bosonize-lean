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

def smallLabel (j : Fin 8) : A05.JointPartitions (Fin 2) 2 :=
  ⟨fun ν => ⟨⟨(smallParts j ν).sum, by fin_cases j <;> fin_cases ν <;> decide⟩,
    ⟨((smallParts j ν) : Multiset ℕ), by fin_cases j <;> fin_cases ν <;> decide, rfl⟩⟩,
      by fin_cases j <;> decide⟩

theorem small_label_bijective : Function.Bijective smallLabel := by
  have h2 (p : Nat.Partition 2) : p.parts = {2} ∨ p.parts = {1,1} := by
    by_cases hm : 2 ∈ p.parts
    · left
      let e := Nat.Partition.partitionWithPartEquiv (n := 2) (a := 2) (by norm_num) (by norm_num)
      have he : p.parts.erase 2 = 0 := by
        simpa only [e, Nat.Partition.partitionWithPartEquiv_apply_parts] using
          Nat.Partition.partition_zero_parts (e ⟨p, hm⟩)
      simpa [he] using (Multiset.cons_erase hm).symm
    · right
      have hall : ∀ a ∈ p.parts, a = 1 := by
        intro a ha
        have hlo := p.parts_pos ha
        have hhi := p.le_of_mem_parts ha
        have hne : a ≠ 2 := by intro h; subst a; exact hm ha
        omega
      have he := Multiset.eq_replicate_card.mpr hall
      have hc : p.parts.card = 2 := by
        have hh := congrArg Multiset.sum he
        simpa [p.parts_sum] using hh.symm
      simpa [hc] using he
  have hlist (p : Ch11.BudgetPartitions 2) :
      Ch11.partitionList p.2 = [] ∨ Ch11.partitionList p.2 = [1] ∨
      Ch11.partitionList p.2 = [1,1] ∨ Ch11.partitionList p.2 = [2] := by
    rcases p with ⟨⟨n,hn⟩,p⟩
    interval_cases n
    · simp [Ch11.partitionList]
    · simp [Ch11.partitionList]
    · rcases h2 p with he|he
      · right; right; right; simp [Ch11.partitionList, he]
      · right; right; left
        change p.parts.sort (· ≥ ·) = [1,1]
        rw [he]
        rw [Multiset.insert_eq_cons, Multiset.sort_cons 1 {1} (· ≥ ·) (by simp)]
        simp
  have hinj : Function.Injective (fun p : Ch11.BudgetPartitions 2 => Ch11.partitionList p.2) := by
    rintro ⟨E,p⟩ ⟨F,q⟩ hh
    dsimp only at hh
    have hef : E = F := Fin.ext (by
      rw [← Ch11.partition_list_sum p, ← Ch11.partition_list_sum q, hh])
    subst F
    congr 1
    apply Nat.Partition.ext
    rw [← Ch11.partition_list_multiset p, ← Ch11.partition_list_multiset q, hh]
  have hparts (j : Fin 8) (ν : Fin 2) :
      Ch11.partitionList ((smallLabel j).val ν).2 = smallParts j ν := by
    fin_cases j <;> fin_cases ν <;> simp [smallLabel, smallParts, Ch11.partitionList]
  constructor
  · intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [smallLabel, smallParts, funext_iff]
    all_goals have hc := congrArg Multiset.card he; norm_num at hc
  · intro p
    have heq (j : Fin 8) (hr : smallParts j 0 = Ch11.partitionList (p.val 0).2)
        (hl : smallParts j 1 = Ch11.partitionList (p.val 1).2) : smallLabel j = p := by
      apply Subtype.ext
      funext ν
      apply hinj
      dsimp only
      rw [hparts]
      fin_cases ν
      · exact hr
      · exact hl
    have hsum : (Ch11.partitionList (p.val 0).2).sum +
        (Ch11.partitionList (p.val 1).2).sum ≤ 2 := by
      rw [Ch11.partition_list_sum, Ch11.partition_list_sum]
      simpa [Fin.sum_univ_two] using p.property
    rcases hlist (p.val 0) with hr|hr|hr|hr <;>
      rcases hlist (p.val 1) with hl|hl|hl|hl
    all_goals try {simp only [hr, hl, List.sum_cons, List.sum_nil] at hsum; omega}
    all_goals first
      | exact ⟨0, heq 0 (by simpa [smallParts] using hr.symm) (by simpa [smallParts] using hl.symm)⟩
      | exact ⟨1, heq 1 (by simpa [smallParts] using hr.symm) (by simpa [smallParts] using hl.symm)⟩
      | exact ⟨2, heq 2 (by simpa [smallParts] using hr.symm) (by simpa [smallParts] using hl.symm)⟩
      | exact ⟨3, heq 3 (by simpa [smallParts] using hr.symm) (by simpa [smallParts] using hl.symm)⟩
      | exact ⟨4, heq 4 (by simpa [smallParts] using hr.symm) (by simpa [smallParts] using hl.symm)⟩
      | exact ⟨5, heq 5 (by simpa [smallParts] using hr.symm) (by simpa [smallParts] using hl.symm)⟩
      | exact ⟨6, heq 6 (by simpa [smallParts] using hr.symm) (by simpa [smallParts] using hl.symm)⟩
      | exact ⟨7, heq 7 (by simpa [smallParts] using hr.symm) (by simpa [smallParts] using hl.symm)⟩

theorem small_partition_state (j : Fin 8) :
    A05.partitionState 8 smallCharges (smallLabel j) =
      A05.wordState 8 smallCharges (smallParts j) := by
  unfold A05.partitionState
  congr 1
  funext ν
  fin_cases j <;> fin_cases ν <;> simp [smallLabel, smallParts, Ch11.partitionList]

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
