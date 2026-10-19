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

theorem small_eta_algebra :
    smallEta * (17 + Real.sqrt 514) = 15 ∧
    15 * smallEta = Real.sqrt 514 - 17 ∧
    15 * smallEta ^ 2 + 34 * smallEta = 15 ∧
    smallEta ^ 2 / (1 + smallEta ^ 2) = (1 - 17 / Real.sqrt 514) / 2 ∧
    smallEta / (1 + smallEta ^ 2) = 15 / (2 * Real.sqrt 514) := by
  have hD : (Real.sqrt 514) ^ 2 = 514 := Real.sq_sqrt (by norm_num)
  have hDpos : 0 < Real.sqrt 514 := Real.sqrt_pos.mpr (by norm_num)
  have hden : 17 + Real.sqrt 514 ≠ 0 := by positivity
  have h1 : smallEta * (17 + Real.sqrt 514) = 15 := by
    unfold smallEta
    field_simp
  have h2 : 15 * smallEta = Real.sqrt 514 - 17 := by
    unfold smallEta
    field_simp
    nlinarith
  have h3 : 15 * smallEta ^ 2 + 34 * smallEta = 15 := by nlinarith [h1]
  refine ⟨h1,h2,h3,?_,?_⟩
  · have he : 1 + smallEta ^ 2 ≠ 0 := by positivity
    field_simp
    nlinarith [h1,h2,h3]
  · have he : 1 + smallEta ^ 2 ≠ 0 := by positivity
    field_simp
    nlinarith [h1,h2,h3]

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

set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
/-- Complete operator action, including all six complementary eigenvectors. -/
theorem small_matrix_action (j : Fin 8) :
    smallHamiltonian (smallVector j) = ∑ i : Fin 8, smallMatrix i j • smallVector i := by
  set_option maxRecDepth 2000 in
  set_option maxHeartbeats 2000000 in
  have hentries (i j : Fin 8) :
      inner ℂ (smallVector i) (smallHamiltonian (smallVector j)) = smallMatrix i j := by
    let v (k : Fin 8) := inclusion 8 smallCharges 2 (smallVector k)
    have hv (k : Fin 8) : v k ∈ A05.jointBudget 8 smallCharges 2 := (smallVector k).property
    have hg (k l : Fin 8) : inner ℂ (v k) (v l) = if k = l then 1 else 0 :=
      orthonormal_iff_ite.mp small_orthonormal k l
    rw [smallHamiltonian, budgetHamiltonian, compression_inner]
    change inner ℂ (v i) (ambientHamiltonian 8 2 1 (32*Real.pi) (30*Real.pi)
      (Ch17.canonicalMu 8 1) smallBranches (v j)) = _
    rw [ambientHamiltonian, Ch17.luttingerBosonizedHamiltonian, LinearMap.add_apply,
      inner_add_right, Ch17.zero_mode_op_on_budget 8 2 1 (32*Real.pi) (30*Real.pi)
        (Ch17.canonicalMu 8 1) smallBranches smallCharges (v j) (hv j)]
    simp only [Ch17.zeroModeEnergyScalar, smallCharges, Int.cast_zero, mul_zero, zero_mul,
      add_zero, zero_add, zero_div, sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Complex.ofReal_zero, mul_zero]
    have hv1 : Ch17.v1Velocity 1 (32*Real.pi) = 17 := Ch18.concrete_velocity_match.1.symm
    have hv2 : Ch17.v2Velocity (30*Real.pi) = 15 := Ch18.concrete_velocity_match.2.symm
    have hcre (ν : Fin 2) (m : ℕ) : A05.rho 8 ν (m : ℤ) =
        LinearMap.adjoint (A05.rho 8 ν (-(m : ℤ))) := by rw [A05.rho_adjoint, neg_neg]
    have hnum (ν : Fin 2) (m : ℕ) :
        inner ℂ (v i) ((A05.rho 8 ν (m : ℤ) * A05.rho 8 ν (-(m : ℤ))) (v j)) =
          inner ℂ (A05.rho 8 ν (-(m : ℤ)) (v i)) (A05.rho 8 ν (-(m : ℤ)) (v j)) := by
      rw [hcre, Module.End.mul_apply, LinearMap.adjoint_inner_right]
    have hpair (m : ℕ) :
        inner ℂ (v i) ((A05.rho 8 (0 : Fin 2) (m : ℤ) * A05.rho 8 (1 : Fin 2) (m : ℤ)) (v j)) =
          inner ℂ (A05.rho 8 (1 : Fin 2) (-(m : ℤ)) (A05.rho 8 (0 : Fin 2) (-(m : ℤ)) (v i))) (v j) := by
      rw [hcre, Module.End.mul_apply, LinearMap.adjoint_inner_right, hcre,
        LinearMap.adjoint_inner_right]
    unfold Ch17.luttingerOscillatorOp
    rw [hv1, hv2]
    norm_num only [show Finset.Icc 1 2 = {1,2} by decide, Finset.sum_insert,
      Finset.mem_singleton, Nat.reduceEqDiff, not_false_eq_true, Finset.sum_singleton]
    simp only [A07Interactions.pairingMode, smallBranches, Ch18.concreteBranches, Ch16.standardBranches,
      LinearMap.smul_apply, LinearMap.add_apply, inner_add_right, inner_smul_right]
    rw [hnum, hnum, hpair, hnum, hnum, hpair]
    simp only [Module.End.mul_apply]
    simp only [v, small_current_lowering _ 1 (Or.inl rfl), small_current_lowering _ 2 (Or.inr rfl),
      map_smul, inner_smul_left, inner_smul_right]
    simp only [v] at hg
    simp only [hg]
    have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by norm_cast; norm_num
    fin_cases i <;> fin_cases j <;>
      norm_num [smallLowerTarget, smallLowerCoefficient, smallMatrix, Complex.star_def]
    all_goals ring_nf
    all_goals simp only [hs]
    all_goals ring
  let b := OrthonormalBasis.mk small_orthonormal small_complete.ge
  have ht := b.sum_repr' (smallHamiltonian (smallVector j))
  simpa only [b, OrthonormalBasis.coe_mk, hentries] using ht.symm


/-- All eight eigenvalues with multiplicity, on a complete orthonormal basis. -/
theorem small_spectral_basis :
    ∃ b : OrthonormalBasis (Fin 8) ℂ (Budget 8 smallCharges 2),
      ∀ j, smallHamiltonian (b j) = (smallEigenvalue j : ℂ) • b j := by
  let v := OrthonormalBasis.mk small_orthonormal small_complete.ge
  let a : ℝ := (Real.sqrt (1 + smallEta ^ 2))⁻¹
  have ha : a ^ 2 * (1 + smallEta ^ 2) = 1 := by
    dsimp [a]
    have hp : (0 : ℝ) < 1 + smallEta ^ 2 := by positivity
    field_simp
    rw [Real.sq_sqrt hp.le]
  have hA (j : Fin 8) : smallHamiltonian (v j) = ∑ i : Fin 8,
      (((Real.pi / 8 : ℝ) : ℂ) * (if (i=0 ∧ j=5) ∨ (i=5 ∧ j=0) then 15 else
        if i=j then if i=0 then 0 else if i=1 ∨ i=2 then 17 else 34 else 0)) • v i := by
    simpa only [v, OrthonormalBasis.coe_mk, smallMatrix] using small_matrix_action j
  obtain ⟨b, hz, hb⟩ := finite_plane_diagonalization v smallHamiltonian (Real.pi / 8)
    smallEta (Real.sqrt 514) a ha small_eta_algebra.1 small_eta_algebra.2.1 hA
  have hzero : b 0 = smallPsi := by
    simpa only [v, OrthonormalBasis.coe_mk, a, smallPsi] using hz
  have heval (j : Fin 8) : Real.pi / 8 * (if j=0 then 17-Real.sqrt 514 else
      if j=5 then 17+Real.sqrt 514 else if j=1 ∨ j=2 then 17 else 34) = smallEigenvalue j := by
    unfold smallEigenvalue smallEnergy
    split_ifs <;> ring
  have heig (j : Fin 8) : smallHamiltonian (b j) = (smallEigenvalue j : ℂ) • b j := by
    simpa only [heval] using hb j
  exact ⟨b, heig⟩


theorem small_ground : ‖smallPsi‖ = 1 ∧
    smallHamiltonian smallPsi = (smallEnergy : ℂ) • smallPsi ∧
    (∀ v : Budget 8 smallCharges 2,
      smallEnergy * ‖v‖ ^ 2 ≤ (inner ℂ v (smallHamiltonian v)).re) ∧ smallEnergy < 0 := by
  have hbound {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (b : OrthonormalBasis (Fin 8) ℂ E) (A : Module.End ℂ E)
      (e : Fin 8 → ℝ) (e0 : ℝ) (he : ∀ j, e0 ≤ e j)
      (hA : ∀ j, A (b j) = (e j : ℂ) • b j) (x : E) :
      e0 * ‖x‖^2 ≤ (inner ℂ x (A x)).re := by
    have hg := orthonormal_iff_ite.mp b.orthonormal
    have hcoord (i : Fin 8) : inner ℂ (b i) (A x) = (e i : ℂ) * inner ℂ (b i) x := by
      conv_lhs => rw [← b.sum_repr' x]
      simp only [map_sum, map_smul, hA, inner_sum, inner_smul_right, hg]
      simp [mul_comm]
    have hterm (j : Fin 8) :
        (inner ℂ x (b j) * inner ℂ (b j) (A x)).re = e j * ‖inner ℂ x (b j)‖^2 := by
      rw [hcoord]
      calc
        _ = ((e j : ℂ) * (inner ℂ x (b j) * inner ℂ (b j) x)).re := by congr 1; ring
        _ = _ := by
          rw [Complex.mul_re]
          simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          have hn := inner_mul_symm_re_eq_norm (𝕜 := ℂ) x (b j)
          have hn' : (inner ℂ x (b j) * inner ℂ (b j) x).re = ‖inner ℂ x (b j) * inner ℂ (b j) x‖ := hn
          rw [hn', norm_mul, norm_inner_symm (b j) x, pow_two]
    calc
      _ = ∑ j, e0 * ‖inner ℂ x (b j)‖^2 := by rw [← Finset.mul_sum, b.sum_sq_norm_inner_left]
      _ ≤ ∑ j, e j * ‖inner ℂ x (b j)‖^2 := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (he j) (sq_nonneg _)
      _ = _ := by rw [← b.sum_inner_mul_inner x (A x), Complex.re_sum]; simp only [hterm]
  let v := OrthonormalBasis.mk small_orthonormal small_complete.ge
  let a : ℝ := (Real.sqrt (1 + smallEta ^ 2))⁻¹
  have ha : a ^ 2 * (1 + smallEta ^ 2) = 1 := by
    dsimp [a]
    have hp : (0 : ℝ) < 1 + smallEta ^ 2 := by positivity
    field_simp
    rw [Real.sq_sqrt hp.le]
  have hA (j : Fin 8) : smallHamiltonian (v j) = ∑ i : Fin 8,
      (((Real.pi / 8 : ℝ) : ℂ) * (if (i=0 ∧ j=5) ∨ (i=5 ∧ j=0) then 15 else
        if i=j then if i=0 then 0 else if i=1 ∨ i=2 then 17 else 34 else 0)) • v i := by
    simpa only [v, OrthonormalBasis.coe_mk, smallMatrix] using small_matrix_action j
  obtain ⟨b, hz, hb⟩ := finite_plane_diagonalization v smallHamiltonian (Real.pi / 8)
    smallEta (Real.sqrt 514) a ha small_eta_algebra.1 small_eta_algebra.2.1 hA
  have hzero : b 0 = smallPsi := by
    simpa only [v, OrthonormalBasis.coe_mk, a, smallPsi] using hz
  have heval (j : Fin 8) : Real.pi / 8 * (if j=0 then 17-Real.sqrt 514 else
      if j=5 then 17+Real.sqrt 514 else if j=1 ∨ j=2 then 17 else 34) = smallEigenvalue j := by
    unfold smallEigenvalue smallEnergy
    split_ifs <;> ring
  have heig (j : Fin 8) : smallHamiltonian (b j) = (smallEigenvalue j : ℂ) • b j := by
    simpa only [heval] using hb j
  have hDpos : 0 < Real.sqrt 514 := Real.sqrt_pos.mpr (by norm_num)
  have hDsq : (Real.sqrt 514)^2 = 514 := Real.sq_sqrt (by norm_num)
  have hD : 17 < Real.sqrt 514 := by nlinarith
  have hneg : smallEnergy < 0 := mul_neg_of_pos_of_neg
    (div_pos Real.pi_pos (by norm_num)) (sub_neg.mpr hD)
  have hmin (j : Fin 8) : smallEnergy ≤ smallEigenvalue j := by
    unfold smallEigenvalue
    split_ifs
    · exact le_rfl
    all_goals exact le_trans hneg.le (by positivity)
  refine ⟨?_, ?_, ?_, hneg⟩
  · simpa only [hzero] using b.orthonormal.norm_eq_one 0
  · simpa only [hzero, smallEigenvalue, ite_true] using heig 0
  · exact hbound b smallHamiltonian smallEigenvalue smallEnergy hmin heig


set_option maxHeartbeats 2000000 in
theorem small_number_moment :
    extendedState (E := Budget 8 smallCharges 2) (inclusion 8 smallCharges 2) smallPsi
      (A05.rho 8 (smallBranches.rightSpecies) 1 *
        A05.rho 8 (smallBranches.rightSpecies) (-1)) =
      (((1 - 17 / Real.sqrt 514) / 2 : ℝ) : ℂ) := by
  set_option maxHeartbeats 2000000 in
    let z (j : Fin 8) := inclusion 8 smallCharges 2 (smallVector j)
    let a : ℝ := (Real.sqrt (1 + smallEta ^ 2))⁻¹
    have hpsi : inclusion 8 smallCharges 2 smallPsi =
        (a : ℂ) • (z 0 - (smallEta : ℂ) • z 5) := by
      simp only [smallPsi, map_smul, map_sub]
      rfl
    have hg (j k : Fin 8) : inner ℂ (z j) (z k) = if j = k then 1 else 0 :=
      orthonormal_iff_ite.mp small_orthonormal j k
    have hr0 : A05.rho 8 (0 : Fin 2) (-1) (z 0) = 0 := by
      simpa [z, smallLowerCoefficient] using small_current_lowering 0 1 (Or.inl rfl) 0
    have hr5 : A05.rho 8 (0 : Fin 2) (-1) (z 5) = z 2 := by
      simpa [z, smallLowerCoefficient, smallLowerTarget] using small_current_lowering 0 1 (Or.inl rfl) 5
    have hcre : A05.rho 8 (0 : Fin 2) 1 = LinearMap.adjoint (A05.rho 8 (0 : Fin 2) (-1)) := by
      rw [A05.rho_adjoint]; rfl
    rw [extended_state_vector (inclusion 8 smallCharges 2) smallPsi]
    change inner ℂ (inclusion 8 smallCharges 2 smallPsi)
      ((A05.rho 8 (0 : Fin 2) 1 * A05.rho 8 (0 : Fin 2) (-1))
        (inclusion 8 smallCharges 2 smallPsi)) = _
    rw [hcre, Module.End.mul_apply, LinearMap.adjoint_inner_right, hpsi]
    simp only [map_smul, map_sub, hr0, hr5, zero_sub, inner_smul_left, inner_smul_right,
      inner_neg_left, inner_neg_right, hg, ite_true, mul_one, Complex.conj_ofReal]
    have ha : a ^ 2 * (1 + smallEta ^ 2) = 1 := by
      dsimp [a]
      have hp : (0 : ℝ) < 1 + smallEta ^ 2 := by positivity
      field_simp
      rw [Real.sq_sqrt hp.le]
    have he := small_eta_algebra.2.2.2.1
    have ha' : a ^ 2 = 1 / (1 + smallEta ^ 2) := (eq_div_iff (by positivity)).mpr ha
    have hres : a * (smallEta * (a * smallEta)) = (1 - 17 / Real.sqrt 514) / 2 := by
      calc
        _ = a ^ 2 * smallEta ^ 2 := by ring
        _ = smallEta ^ 2 / (1 + smallEta ^ 2) := by rw [ha']; ring
        _ = _ := he
    norm_cast
    convert hres using 1
    ring

set_option maxHeartbeats 2000000 in
theorem small_pair_moment :
    extendedState (E := Budget 8 smallCharges 2) (inclusion 8 smallCharges 2) smallPsi
      (A05.rho 8 (smallBranches.rightSpecies) 1 *
        A05.rho 8 (smallBranches.leftSpecies) 1) =
      ((-15 / (2 * Real.sqrt 514) : ℝ) : ℂ) := by
  let z (j : Fin 8) := inclusion 8 smallCharges 2 (smallVector j)
  let a : ℝ := (Real.sqrt (1 + smallEta ^ 2))⁻¹
  have hpsi : inclusion 8 smallCharges 2 smallPsi =
      (a : ℂ) • (z 0 - (smallEta : ℂ) • z 5) := by
    simp only [smallPsi, map_smul, map_sub]
    rfl
  have hg (j k : Fin 8) : inner ℂ (z j) (z k) = if j = k then 1 else 0 :=
    orthonormal_iff_ite.mp small_orthonormal j k
  have hr0 : A05.rho 8 (0 : Fin 2) (-1) (z 0) = 0 := by
    simpa [z, smallLowerCoefficient] using small_current_lowering 0 1 (Or.inl rfl) 0
  have hr5 : A05.rho 8 (0 : Fin 2) (-1) (z 5) = z 2 := by
    simpa [z, smallLowerCoefficient, smallLowerTarget] using small_current_lowering 0 1 (Or.inl rfl) 5
  have hl2 : A05.rho 8 (1 : Fin 2) (-1) (z 2) = z 0 := by
    simpa [z, smallLowerCoefficient, smallLowerTarget] using small_current_lowering 1 1 (Or.inl rfl) 2
  have hcre (ν : Fin 2) : A05.rho 8 ν 1 = LinearMap.adjoint (A05.rho 8 ν (-1)) := by
    rw [A05.rho_adjoint]; rfl
  rw [extended_state_vector (inclusion 8 smallCharges 2) smallPsi]
  change inner ℂ (inclusion 8 smallCharges 2 smallPsi)
    ((A05.rho 8 (0 : Fin 2) 1 * A05.rho 8 (1 : Fin 2) 1)
      (inclusion 8 smallCharges 2 smallPsi)) = _
  rw [hcre 0, Module.End.mul_apply, LinearMap.adjoint_inner_right, hcre 1,
    LinearMap.adjoint_inner_right, hpsi]
  simp only [map_smul, map_sub, map_neg, hr0, hr5, hl2, zero_sub,
    inner_sub_right, inner_smul_left, inner_smul_right, inner_neg_left,
    hg, show (0 : Fin 8) ≠ 5 by decide, ite_true, ite_false, mul_zero, sub_zero, mul_one, Complex.conj_ofReal]
  have ha : a ^ 2 * (1 + smallEta ^ 2) = 1 := by
    dsimp [a]
    have hp : (0 : ℝ) < 1 + smallEta ^ 2 := by positivity
    field_simp
    rw [Real.sq_sqrt hp.le]
  have he := small_eta_algebra.2.2.2.2
  have ha' : a ^ 2 = 1 / (1 + smallEta ^ 2) := (eq_div_iff (by positivity)).mpr ha
  have hres : -(a * smallEta * a) = -15 / (2 * Real.sqrt 514) := by
    calc
      _ = -(a ^ 2 * smallEta) := by ring
      _ = -(smallEta / (1 + smallEta ^ 2)) := by rw [ha']; ring
      _ = _ := by rw [he]; ring
  norm_cast
  convert hres using 1 <;> norm_num <;> ring


theorem small_number_discrepancy :
    extendedState (E := Budget 8 smallCharges 2) (inclusion 8 smallCharges 2) smallPsi
      (A05.rho 8 smallBranches.rightSpecies 1 * A05.rho 8 smallBranches.rightSpecies (-1)) ≠
      A08.omegaP 2 Ch18.concretePair
        (A08.creatorGen 2 .right 0 * A08.annihilatorGen 2 .right 0) := by
  have ho : A08.omegaP 2 Ch18.concretePair
      (A08.creatorGen 2 .right 0 * A08.annihilatorGen 2 .right 0) = (9/16 : ℂ) := by
    have hh := V1S1.generator_contraction 2 Ch18.concretePair (true,.right,0) (false,.right,0)
    norm_num [V1S1.contraction, V1S1.linearElement, V1S1.formOfGenerator,
      V1S1.generatorContractionExpected, A08.creatorGen, A08.annihilatorGen,
      Ch18.concretePair, Ch18.HyperbolicPair.ofParams, Ch18.concreteParams] at hh ⊢
    exact hh
  rw [small_number_moment, ho]
  intro he
  have hr := congrArg Complex.re he
  norm_num at hr
  have hDpos : 0 < Real.sqrt 514 := Real.sqrt_pos.mpr (by norm_num)
  have hp : 0 < 17 / Real.sqrt 514 := div_pos (by norm_num) hDpos
  linarith

theorem small_pair_discrepancy :
    extendedState (E := Budget 8 smallCharges 2) (inclusion 8 smallCharges 2) smallPsi
      (A05.rho 8 smallBranches.rightSpecies 1 * A05.rho 8 smallBranches.leftSpecies 1) ≠
      A08.omegaP 2 Ch18.concretePair
        (A08.creatorGen 2 .right 0 * A08.creatorGen 2 .left 0) := by
  have ho : A08.omegaP 2 Ch18.concretePair
      (A08.creatorGen 2 .right 0 * A08.creatorGen 2 .left 0) = (-15/16 : ℂ) := by
    have hh := V1S1.generator_contraction 2 Ch18.concretePair (true,.right,0) (true,.left,0)
    norm_num [V1S1.contraction, V1S1.linearElement, V1S1.formOfGenerator,
      V1S1.generatorContractionExpected, A08.creatorGen, A08.annihilatorGen,
      Ch18.concretePair, Ch18.HyperbolicPair.ofParams, Ch18.concreteParams,
      A07Interactions.oppositeOrientation] at hh ⊢
    exact hh
  rw [small_pair_moment, ho]
  intro he
  have hr : (-15 / (2 * Real.sqrt 514) : ℝ) = -15/16 := by exact_mod_cast he
  have hDpos : 0 < Real.sqrt 514 := Real.sqrt_pos.mpr (by norm_num)
  have hD : (Real.sqrt 514)^2 = 514 := Real.sq_sqrt (by norm_num)
  have hbig : 15 < Real.sqrt 514 := by nlinarith
  have hp : 15 / (2 * Real.sqrt 514) < (1/2 : ℝ) := (div_lt_iff₀ (by positivity)).mpr (by linarith)
  rw [neg_div] at hr
  linarith

end Bosonize.V1S5
