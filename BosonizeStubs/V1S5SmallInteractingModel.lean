import BosonizeStubs.V1S5FiniteGroundState
import Bosonize.Core.V1S1OrderedWick
import Bosonize.Core.V1S4FiniteCurrentComparison

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

theorem current_word_lowering {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h K m : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (ν : σ) (hm : 0 < m) (hmK : m ≤ K) (hR : A05.r2 h K Ns)
    (parts : σ → List ℕ) (hpos : ∀ η n, n ∈ parts η → 0 < n)
    (hE : ∀ η, (parts η).sum ≤ K) :
    A05.rho h ν (-(m : ℤ)) (A05.wordState h Ns parts) =
      ((m * (parts ν).count m : ℕ) : ℂ) •
        A05.wordState h Ns (Function.update parts ν ((parts ν).erase m)) := by
  classical
  rw [A05.word_tensor h Ns hN, A05.rho_tensor]
  rw [Ch11.lowering_through_word_erase h hh (Ns ν) (hN ν) K m hm hmK
    (parts ν) (hpos ν) (hE ν) (hR ν)]
  rw [← Nat.cast_smul_eq_nsmul ℂ, V1S4.Support.tensor_update_smul]
  rw [A05.word_tensor h Ns hN]
  congr 1
  congr 1
  funext η
  by_cases he : η = ν
  · subst η
    simp
  · simp [he]

def smallLowerTarget (ν : Fin 2) (m : ℕ) (j : Fin 8) : Fin 8 :=
  if m = 1 then
    if ν = 0 then if j = 3 then 1 else if j = 5 then 2 else 0
    else if j = 4 then 2 else if j = 5 then 1 else 0
  else 0

noncomputable def smallLowerCoefficient (ν : Fin 2) (m : ℕ) (j : Fin 8) : ℂ :=
  if m = 1 then
    if ν = 0 then if j = 1 ∨ j = 5 then 1 else if j = 3 then ((Real.sqrt 2 : ℝ) : ℂ) else 0
    else if j = 2 ∨ j = 5 then 1 else if j = 4 then ((Real.sqrt 2 : ℝ) : ℂ) else 0
  else if m = 2 then
    if (ν = 0 ∧ j = 6) ∨ (ν = 1 ∧ j = 7) then ((Real.sqrt 2 : ℝ) : ℂ) else 0
  else 0

theorem small_parts_lower (ν : Fin 2) (m : ℕ) (hm : m = 1 ∨ m = 2) (j : Fin 8)
    (hc : (smallParts j ν).count m ≠ 0) :
    Function.update (smallParts j) ν ((smallParts j ν).erase m) =
      smallParts (smallLowerTarget ν m j) := by
  fin_cases ν <;> rcases hm with rfl|rfl <;> fin_cases j <;>
    simp_all [smallParts, smallLowerTarget]
  all_goals (funext η; fin_cases η <;> rfl)

theorem small_current_lowering (ν : Fin 2) (m : ℕ) (hm : m = 1 ∨ m = 2) (j : Fin 8) :
    A05.rho 8 ν (-(m : ℤ)) (inclusion 8 smallCharges 2 (smallVector j)) =
      smallLowerCoefficient ν m j • inclusion 8 smallCharges 2
        (smallVector (smallLowerTarget ν m j)) := by
  have hpos : ∀ η n, n ∈ smallParts j η → 0 < n := by
    fin_cases j <;> intro η <;> fin_cases η <;> simp [smallParts]
  have hE : ∀ η, (smallParts j η).sum ≤ 2 := by
    fin_cases j <;> intro η <;> fin_cases η <;> norm_num [smallParts]
  have hR : A05.r2 8 2 smallCharges := by intro η; norm_num [smallCharges]
  change A05.rho 8 ν (-(m : ℤ))
    (smallCoefficient j • A05.wordState 8 smallCharges (smallParts j)) = _
  rw [map_smul, current_word_lowering 8 2 m (by norm_num) smallCharges small_admissible ν
    (by omega) (by omega) hR (smallParts j) hpos hE, smul_smul]
  by_cases hc : (smallParts j ν).count m = 0
  · simp only [hc, mul_zero, Nat.cast_zero, mul_zero, zero_smul]
    have hcoef : smallLowerCoefficient ν m j = 0 := by
      fin_cases ν <;> rcases hm with rfl|rfl <;> fin_cases j <;>
        simp_all [smallParts, smallLowerCoefficient]
    rw [hcoef, zero_smul]
  · rw [small_parts_lower ν m hm j hc]
    change (smallCoefficient j * ↑(m * (smallParts j ν).count m)) •
      A05.wordState 8 smallCharges (smallParts (smallLowerTarget ν m j)) =
      smallLowerCoefficient ν m j • (smallCoefficient (smallLowerTarget ν m j) • _)
    rw [smul_smul]
    congr 1
    have hnz : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
    have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by norm_cast; norm_num
    fin_cases ν <;> rcases hm with rfl|rfl <;> fin_cases j <;>
      simp_all [smallParts, smallLowerTarget, smallLowerCoefficient, smallCoefficient]
    all_goals field_simp
    all_goals linear_combination -hsq

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

theorem small_orthonormal : Orthonormal ℂ smallVector := by
  have hR2 : A05.r2 8 2 smallCharges := by intro ν; norm_num [smallCharges]
  have hN (j : Fin 8) : (A05.jointNormalization (smallLabel j) : ℂ) *
      star (smallCoefficient j) * smallCoefficient j = 1 := by
    have hnz : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
    have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by norm_cast; norm_num
    unfold A05.jointNormalization smallLabel
    fin_cases j <;>
      norm_num [smallParts, Fin.prod_univ_two, Ch11.partitionNormalization,
        Ch11.hallFactor, smallCoefficient, Complex.star_def]
    all_goals field_simp
    all_goals linear_combination -hsq
  rw [orthonormal_iff_ite]
  intro i j
  change inner ℂ (smallCoefficient i • A05.wordState 8 smallCharges (smallParts i))
    (smallCoefficient j • A05.wordState 8 smallCharges (smallParts j)) = _
  rw [← small_partition_state i, ← small_partition_state j,
    inner_smul_left, inner_smul_right, A05.partition_gram 8 (by norm_num) smallCharges
      small_admissible 2 hR2]
  by_cases he : i = j
  · subst j
    simp only [ite_true]
    simpa only [Complex.star_def, mul_comm, mul_left_comm, mul_assoc] using hN i
  · have hne : smallLabel i ≠ smallLabel j := by
      intro h
      exact he (small_label_bijective.1 h)
    simp [hne, he]

theorem small_complete : Submodule.span ℂ (Set.range smallVector) = ⊤ := by
  let W := Submodule.span ℂ (Set.range smallVector)
  have hR2 : A05.r2 8 2 smallCharges := by intro ν; norm_num [smallCharges]
  obtain ⟨b,hb⟩ := A05.partition_basis 8 (by norm_num) smallCharges small_admissible 2 hR2
  have hvec (j : Fin 8) : smallVector j = smallCoefficient j • b (smallLabel j) := by
    apply Subtype.ext
    change smallCoefficient j • A05.wordState 8 smallCharges (smallParts j) = _
    rw [Submodule.coe_smul, hb, small_partition_state]
  have hc (j : Fin 8) : smallCoefficient j ≠ 0 := by
    unfold smallCoefficient
    split_ifs
    · exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num)))
    · exact one_ne_zero
  have hm (p : A05.JointPartitions (Fin 2) 2) : b p ∈ W := by
    obtain ⟨j,rfl⟩ := small_label_bijective.2 p
    have hmem : smallCoefficient j • b (smallLabel j) ∈ W := by
      rw [← hvec]
      exact Submodule.subset_span (Set.mem_range_self j)
    have hh := W.smul_mem (smallCoefficient j)⁻¹ hmem
    simpa only [smul_smul, inv_mul_cancel₀ (hc j), one_smul] using hh
  apply top_unique
  intro v _
  rw [← b.sum_repr v]
  exact Submodule.sum_mem W (fun p _ => W.smul_mem _ (hm p))

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
