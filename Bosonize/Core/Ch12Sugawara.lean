module

public import Bosonize.Core.Ch11HaldaneCompleteness

/-! Actual finite Sugawara operator and proved exact budget action.
The positive current is on the left; the lowering current acts first.
Complete finite algebraic proofs; promotion awaits final audits and review. -/
@[expose] public section
namespace Bosonize.Ch12
open scoped BigOperators Classical

abbrev FockSpace (h : ℕ) := Ch07.FockSpace h
abbrev Operators (h : ℕ) := Ch07.Operators h

/-- No cutoff-dependent CCR certificate is built into this finite operator. -/
noncomputable def sugawaraHamiltonian (h M : ℕ) : Operators h :=
  ∑ m ∈ Finset.Icc 1 M, Ch09.rho h (m : ℤ) * Ch09.rho h (-(m : ℤ))

/-- Absolute shifted linear energy minus the energy of the SAME reference sea. -/
noncomputable def physicalRelativeHamiltonian (h : ℕ) (β : ℝ) : Operators h :=
  Ch09.physicalHamiltonian h β -
    (Ch06Ext.physicalOccupationEnergy (2*h) β (Ch05.seaConfiguration (2*h)) : ℂ) • 1

/-- Subtract the actual charge-dependent physical ground polynomial on all occupations. -/
noncomputable def physicalExcitationObservable (h : ℕ) (β : ℝ) : Operators h :=
  physicalRelativeHamiltonian h β - A03.diagonal (fun S =>
    (Ch06Ext.physicalGroundEnergy β (Ch07.relativeCharge h S) : ℂ))

lemma sugawara_zero (h : ℕ) : sugawaraHamiltonian h 0 = 0 := by
  simp [sugawaraHamiltonian]

lemma sugawara_apply (h M : ℕ) (v : FockSpace h) :
    sugawaraHamiltonian h M v =
      ∑ m ∈ Finset.Icc 1 M, Ch09.rho h (m : ℤ) (Ch09.rho h (-(m : ℤ)) v) := by
  simp [sugawaraHamiltonian, LinearMap.sum_apply, Module.End.mul_apply]

lemma sugawara_adjoint (h M : ℕ) :
    LinearMap.adjoint (sugawaraHamiltonian h M) = sugawaraHamiltonian h M := by
  simp only [sugawaraHamiltonian, map_sum, Module.End.mul_eq_comp,
    LinearMap.adjoint_comp, Ch09.rho_adjoint, neg_neg]

/-- A genuinely positive quadratic form on the ambient concrete Hilbert carrier. -/
lemma sugawara_inner (h M : ℕ) (v : FockSpace h) :
    inner ℂ v (sugawaraHamiltonian h M v) =
      ∑ m ∈ Finset.Icc 1 M, inner ℂ (Ch09.rho h (-(m : ℤ)) v)
        (Ch09.rho h (-(m : ℤ)) v) := by
  rw [sugawara_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simpa only [Ch09.rho_adjoint, neg_neg] using
    LinearMap.adjoint_inner_right (Ch09.rho h (-(m : ℤ))) v (Ch09.rho h (-(m : ℤ)) v)

lemma sugawara_ground (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (M : ℕ) :
    sugawaraHamiltonian h M (Ch07.groundKet h N hN) = 0 := by
  rw [sugawara_apply]
  apply Finset.sum_eq_zero
  intro m hm
  have hpos : 0 < (m : ℤ) := by have := (Finset.mem_Icc.mp hm).1; omega
  rw [Ch09.rho_lowering_ground h hh N hN (m : ℤ) hpos, map_zero]

/-- Grading removes these terms before any current pull-through is attempted. -/
lemma inactive_mode_zero (h : ℕ) (hh : 0 < h) (N : ℤ) (K m : ℕ)
    (hm : K < m) (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    (Ch09.rho h (m : ℤ) * Ch09.rho h (-(m : ℤ))) v = 0 := by
  rw [Module.End.mul_apply,
    Ch09.rho_lowering_budget_zero h hh (m : ℤ) N (K : ℤ) (by omega) v hv,
    map_zero]

/-- Cutoff stability requires no R2 margin and no upper bound on M. -/
lemma sugawara_cutoff_budget (h : ℕ) (hh : 0 < h) (N : ℤ) (K M : ℕ)
    (hM : K ≤ M) (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    sugawaraHamiltonian h M v = sugawaraHamiltonian h K v := by
  simp only [sugawaraHamiltonian, LinearMap.sum_apply]
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hM)
  intro m hm hn
  have hpos := (Finset.mem_Icc.mp hm).1
  have hlarge : K < m := by
    by_contra hle
    exact hn (Finset.mem_Icc.mpr ⟨hpos, by omega⟩)
  exact inactive_mode_zero h hh N K m hlarge v hv

lemma sugawara_cutoff_independent (h : ℕ) (hh : 0 < h) (N : ℤ) (K M M' : ℕ)
    (hM : K ≤ M) (hM' : K ≤ M') (v : FockSpace h)
    (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    sugawaraHamiltonian h M v = sugawaraHamiltonian h M' v := by
  rw [sugawara_cutoff_budget h hh N K M hM v hv,
    sugawara_cutoff_budget h hh N K M' hM' v hv]

/-- Restore each erased occurrence using globally commuting positive modes.
The count can be zero; there is no spurious membership assumption on m. -/
lemma density_bilinear_word (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K m : ℕ) (hm : 0 < m) (hmK : m ≤ K)
    (parts : List ℕ) (hE : parts.sum ≤ K)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    (Ch09.rho h (m : ℤ) * Ch09.rho h (-(m : ℤ))) (Ch11.wordState h N hN parts) =
      ((m*parts.count m : ℕ) : ℂ) • Ch11.wordState h N hN parts := by
  have hpull (xs : List ℕ) (hxs : xs.sum≤K) :
      Ch09.rho h (-(m : ℤ)) (Ch11.wordState h N hN xs) =
        ((m : ℂ)*(xs.count m : ℂ)) • Ch11.wordState h N hN (xs.erase m) := by
    induction xs with
    | nil => simpa [Ch11.word_state_nil] using Ch09.rho_lowering_ground h hh N hN (m : ℤ) (by omega)
    | cons n xs ih =>
      have hs : n+xs.sum≤K := by simpa using hxs
      have hmargin : |-(m : ℤ)|+|(n : ℤ)|+(xs.sum : ℤ)+|N|≤(h : ℤ) := by
        rw [abs_neg, abs_of_nonneg (by omega : 0≤(m : ℤ)), abs_of_nonneg (by omega : 0≤(n : ℤ))]
        have hx := Ch11.right_remainder_margin h K m n N xs hmK hs hR2
        exact hx
      have hc := Ch10.rho_signed_ccr h hh (-(m : ℤ)) (n : ℤ) N (xs.sum : ℤ) hmargin
        (Ch11.wordState h N hN xs) (Ch11.word_state_mem_budget h hh N hN xs xs.sum le_rfl)
      have he : Ch10.schwingerCoefficient (-(m : ℤ)) (n : ℤ) = (if m=n then (m : ℂ) else 0) := by
        unfold Ch10.schwingerCoefficient
        by_cases hmn : m=n
        · simp [hmn]
        · have hi : -(m : ℤ)+(n : ℤ)≠0 := by omega
          simp [hmn, hi]
      rw [he] at hc
      change Ch09.rho h (-(m : ℤ)) (Ch09.rho h (n : ℤ) (Ch11.wordState h N hN xs)) -
        Ch09.rho h (n : ℤ) (Ch09.rho h (-(m : ℤ)) (Ch11.wordState h N hN xs)) = _ at hc
      have hswap := (sub_eq_iff_eq_add.mp hc)
      rw [Ch11.word_state_cons, hswap, ih (by omega), map_smul]
      by_cases hmn : n=m
      · subst n
        simp only [List.erase_cons_head, List.count_cons_self, ite_true]
        by_cases hmem : m ∈ xs
        · rw [← Ch11.word_state_cons_erase h m N hN xs hmem, ← add_smul]
          congr 1
          push_cast
          ring
        · have hz : xs.count m=0 := List.count_eq_zero.mpr hmem
          simp [hz]
      · have hmn' : m≠n := Ne.symm hmn
        simp only [hmn', ite_false, zero_smul, zero_add]
        have her : (n::xs).erase m=n::xs.erase m := List.erase_cons_tail (by simp [hmn])
        simp only [List.count_cons, beq_iff_eq, hmn, ite_false, Nat.add_zero, her, Ch11.word_state_cons]
  rw [Module.End.mul_apply, hpull parts hE, map_smul]
  by_cases hmem : m ∈ parts
  · rw [← Ch11.word_state_cons_erase h m N hN parts hmem]
    simp only [Nat.cast_mul]
  · have hz : parts.count m=0 := List.count_eq_zero.mpr hmem
    simp [hz]

lemma positive_word_weight (K : ℕ) (parts : List ℕ)
    (hE : parts.sum ≤ K) :
    ∑ m ∈ Finset.Icc 1 K, m*parts.count m = parts.sum := by
  induction parts with
  | nil => simp
  | cons n parts ih =>
    have hs : n+parts.sum≤K := by simpa using hE
    simp only [List.count_cons, beq_iff_eq, mul_add, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_add_distrib, ih (by omega)]
    by_cases hn : n=0
    · subst n
      simp
    · have hnpos : 1≤n := by omega
      have hnK : n≤K := by omega
      simp [hnpos, hnK, List.sum_cons, Nat.add_comm]

lemma sugawara_word_eigenvalue (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M : ℕ) (hM : K ≤ M)
    (parts : List ℕ) (hE : parts.sum ≤ K)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    sugawaraHamiltonian h M (Ch11.wordState h N hN parts) =
      (parts.sum : ℂ) • Ch11.wordState h N hN parts := by
  rw [sugawara_cutoff_budget h hh N K M hM _ (Ch11.word_state_mem_budget h hh N hN parts K hE), sugawara_apply]
  have he : (∑ m ∈ Finset.Icc 1 K,
      Ch09.rho h (m : ℤ) (Ch09.rho h (-(m : ℤ)) (Ch11.wordState h N hN parts))) =
      ∑ m ∈ Finset.Icc 1 K, ((m*parts.count m : ℕ) : ℂ) • Ch11.wordState h N hN parts := by
    apply Finset.sum_congr rfl
    intro m hm
    exact density_bilinear_word h hh N hN K m (by have := (Finset.mem_Icc.mp hm).1; omega)
      (Finset.mem_Icc.mp hm).2 parts hE hR2
  rw [he, ← Finset.sum_smul]
  congr 1
  exact_mod_cast positive_word_weight K parts hE

lemma sugawara_partition_eigenvalue (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M E : ℕ) (hEK : E ≤ K) (hM : K ≤ M)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) (p : Nat.Partition E) :
    sugawaraHamiltonian h M (Ch11.partitionState h N hN p) =
      (E : ℂ) • Ch11.partitionState h N hN p := by
  simpa only [Ch11.partitionState, Ch11.partition_list_sum] using
    sugawara_word_eigenvalue h hh N hN K M hM (Ch11.partitionList p)
      (by simpa only [Ch11.partition_list_sum] using hEK) hR2

lemma excitation_energy_space (h : ℕ) (N E : ℤ) (v : FockSpace h)
    (hv : v ∈ Ch07.energySpace h N E) :
    Ch07.excitationObservable h v = (E : ℂ) • v := by
  change v ∈ Submodule.span ℂ (A02.ket '' {S | Ch07.relativeCharge h S = N ∧ Ch07.excitationEnergy h S = E}) at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    rcases hw with ⟨S, hS, rfl⟩
    rw [Ch07.excitation_observable_ket, hS.2]
  | zero => simp
  | add x y hx hy hxe hye => simp only [map_add, smul_add, hxe, hye]
  | smul a x hx hxe => simp only [map_smul, hxe, smul_comm a (E : ℂ) x]

lemma excitation_partition_eigenvalue (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (E : ℕ) (p : Nat.Partition E) :
    Ch07.excitationObservable h (Ch11.partitionState h N hN p) =
      (E : ℂ) • Ch11.partitionState h N hN p := by
  exact excitation_energy_space h N (E : ℤ) _ (Ch11.partition_state_mem_energy h hh N hN p)

lemma sugawara_budget_partition_eigenvalue (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M : ℕ) (hM : K ≤ M)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) (p : Ch11.BudgetPartitions K) :
    sugawaraHamiltonian h M (Ch11.budgetPartitionState h N hN p) =
      (p.1.val : ℂ) • Ch11.budgetPartitionState h N hN p := by
  exact sugawara_partition_eigenvalue h hh N hN K M p.1.val
    (Nat.le_of_lt_succ p.1.isLt) hM hR2 p.2

/-- Extend equality across the whole actual CH11 partition basis. -/
theorem sugawara_equivalence (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M : ℕ) (hM : K ≤ M)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ))
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    Ch07.excitationObservable h v = sugawaraHamiltonian h M v := by
  rw [← Ch11.budget_partition_spanning h hh N hN K hR2] at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    rcases hw with ⟨p, rfl⟩
    rw [sugawara_budget_partition_eigenvalue h hh N hN K M hM hR2 p]
    exact excitation_partition_eigenvalue h hh N hN p.1.val p.2
  | zero => simp
  | add x y hx hy hxe hye => simp only [map_add, hxe, hye]
  | smul a x hx hxe => simp only [map_smul, hxe]

lemma relative_energy_budget (h : ℕ) (N : ℤ) (K : ℕ)
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    Ch05.shiftedHamiltonian (2*h) v =
      Ch07.excitationObservable h v + (Ch07.groundEnergy N : ℂ) • v := by
  change v ∈ A03.coordinateSpace _ at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    change Ch07.relativeCharge h S = N ∧ Ch07.excitationEnergy h S ≤ (K : ℤ) at hS
    rw [Ch05.shifted_hamiltonian_ket, Ch07.excitation_observable_ket, ← add_smul]
    congr 1
    simp [Ch07.excitationEnergy, Ch07.relativeEnergy, hS.1]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, smul_add]; abel
  | smul a x _ hx => simp only [map_smul, hx, smul_add, smul_comm a]

lemma ground_energy_complex (N : ℤ) :
    (Ch07.groundEnergy N : ℂ) = (N : ℂ)*((N : ℂ)+1)/2 := by
  have hc : (2 : ℂ) * (Ch07.groundEnergy N : ℂ) = (N : ℂ)*((N : ℂ)+1) := by
    exact_mod_cast Ch07.ground_energy_double N
  linear_combination hc / 2

/-- Same-sea integer ground shift is N(N+1)/2, including negative charges. -/
theorem sugawara_relative_hamiltonian (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M : ℕ) (hM : K ≤ M)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ))
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    Ch05.shiftedHamiltonian (2*h) v =
      (sugawaraHamiltonian h M + ((N : ℂ)*((N : ℂ)+1)/2) • 1) v := by
  rw [relative_energy_budget h N K v hv,
    sugawara_equivalence h hh N hN K M hM hR2 v hv, ground_energy_complex]
  simp

/-- Signed action with separate source and target margins. The target may be any
nonnegative bound dominating the actual signed energy shift K+n. -/
theorem sugawara_signed_commutator (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K J M : ℕ) (n : ℤ)
    (hshift : (K : ℤ)+n ≤ (J : ℤ)) (hMK : K ≤ M) (hMJ : J ≤ M)
    (hsource : 2*(K : ℤ)+|N| ≤ (h : ℤ))
    (htarget : 2*(J : ℤ)+|N| ≤ (h : ℤ))
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    A02.commutator (sugawaraHamiltonian h M) (Ch09.rho h n) v =
      (n : ℂ) • Ch09.rho h n v := by
  have hout := Ch09.rho_budget_map h n N (K : ℤ) v hv
  have houtJ : Ch09.rho h n v ∈ Ch07.fixedBudget h N (J : ℤ) :=
    A03.budget_mono _ _ N ((K : ℤ)+n) (J : ℤ) hshift hout
  have hs := sugawara_equivalence h hh N hN K M hMK hsource v hv
  have ht := sugawara_equivalence h hh N hN J M hMJ htarget _ houtJ
  have hc := congrArg (fun A : Operators h => A v) (Ch09.rho_excitation_commutator h n)
  change sugawaraHamiltonian h M (Ch09.rho h n v) - Ch09.rho h n (sugawaraHamiltonian h M v) = _
  change Ch07.excitationObservable h (Ch09.rho h n v) - Ch09.rho h n (Ch07.excitationObservable h v) = (n : ℂ) • Ch09.rho h n v at hc
  rw [← hs, ← ht]
  exact hc

/-- Nonnegative transfer uses the actual enlarged target K+n.
CH12's n>0 corollary is its positive special case; n=0 is also valid. -/
theorem sugawara_raising_commutator (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M n : ℕ)
    (hM : K+n ≤ M) (hR2 : 2*((K+n : ℕ) : ℤ)+|N| ≤ (h : ℤ))
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    A02.commutator (sugawaraHamiltonian h M) (Ch09.rho h (n : ℤ)) v =
      (n : ℂ) • Ch09.rho h (n : ℤ) v := by
  apply sugawara_signed_commutator h hh N hN K (K+n) M (n : ℤ) (by omega) (by omega) hM (by omega) hR2 v hv

lemma physical_relative_budget (h : ℕ) (hh : 0 < h) (β : ℝ) (N : ℤ) (K : ℕ)
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    physicalRelativeHamiltonian h β v = Ch05.shiftedHamiltonian (2*h) v +
      ((β : ℂ)*(N : ℂ)) • v := by
  change v ∈ A03.coordinateSpace _ at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    change Ch07.relativeCharge h S = N ∧ Ch07.excitationEnergy h S ≤ (K : ℤ) at hS
    simp only [physicalRelativeHamiltonian, Ch09.physicalHamiltonian,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, Ch05.bare_hamiltonian_ket, Ch05.total_number_ket,
      Ch05.shifted_hamiltonian_ket, ← add_smul, ← sub_smul, smul_smul]
    congr 1
    rw [Ch06Ext.physical_energy_shift, Ch05.sea_card_even h hh]
    have hc : (S.card : ℂ)-(h : ℂ) = (N : ℂ) := by
      exact_mod_cast (show (S.card : ℤ)-(h : ℤ)=N from hS.1)
    simp only [Ch05.seaEnergy]
    push_cast
    linear_combination (β : ℂ) * hc
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, smul_add]; abel
  | smul a x _ hx => simp only [map_smul, hx, smul_add, smul_comm a]

/-- Cancellation concerns excitation after subtracting the matching ground
polynomial; neither bare nor relative physical energy is twist independent. -/
lemma physical_excitation_cancel (h : ℕ) (hh : 0 < h) (β : ℝ) :
    physicalExcitationObservable h β = Ch07.excitationObservable h := by
  apply A02.end_ext_basis
  intro S
  simp only [physicalExcitationObservable, physicalRelativeHamiltonian,
    Ch09.physicalHamiltonian, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply, A03.diagonal_ket,
    Ch05.bare_hamiltonian_ket, Ch05.total_number_ket,
    Ch07.excitation_observable_ket, ← add_smul, ← sub_smul, smul_smul]
  congr 1
  rw [Ch06Ext.physical_energy_shift, Ch05.sea_card_even h hh]
  simp only [Ch06Ext.physicalGroundEnergy, Ch07.excitationEnergy, Ch07.relativeEnergy,
    Int.cast_sub, ground_energy_complex, Ch07.relativeCharge]
  simp only [Ch05.seaEnergy]
  push_cast
  ring

theorem physical_sugawara_budget (h : ℕ) (hh : 0 < h) (β : ℝ) (N : ℤ)
    (hN : Ch07.admissible h N) (K M : ℕ) (hM : K ≤ M)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ))
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    physicalRelativeHamiltonian h β v = sugawaraHamiltonian h M v +
      (Ch06Ext.physicalGroundEnergy β N : ℂ) • v := by
  rw [physical_relative_budget h hh β N K v hv,
    relative_energy_budget h N K v hv,
    sugawara_equivalence h hh N hN K M hM hR2 v hv,
    ground_energy_complex, add_assoc, ← add_smul]
  simp only [Ch06Ext.physicalGroundEnergy, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_one, Complex.ofReal_ofNat]

/-- An actual excited vector, not only nonemptiness of the budget. -/
lemma sugawara_excited_witness (h : ℕ) (hh : 0 < h) (K M m : ℕ)
    (hm : 0 < m) (hmK : m ≤ K) (hM : K ≤ M) (hR2 : 2*K ≤ h) :
    ∃ v : FockSpace h, v ∈ Ch07.fixedBudget h 0 (K : ℤ) ∧ v ≠ 0 ∧
      sugawaraHamiltonian h M v = (m : ℂ) • v ∧ sugawaraHamiltonian h M v ≠ 0 := by
  have hN : Ch07.admissible h 0 := by unfold Ch07.admissible; omega
  let v := Ch09.rho h (m : ℤ) (Ch07.vacuumKet h)
  have hnz : v ≠ 0 := Ch09.rho_sea_ne_zero h m hm (by omega)
  have hsea : Ch07.groundKet h 0 hN = Ch07.vacuumKet h := by
    unfold Ch07.groundKet Ch07.vacuumKet
    rw [Ch07.ground_configuration_zero]
    rfl
  have hv : v ∈ Ch07.fixedBudget h 0 (K : ℤ) := by
    apply A03.budget_mono _ _ 0 (0+(m : ℤ)) (K : ℤ) (by omega)
    apply Ch09.rho_budget_map h (m : ℤ) 0 0
    rw [← hsea]
    exact Ch07.ground_ket_mem_budget h hh 0 hN 0
  have he : sugawaraHamiltonian h M v = (m : ℂ) • v := by
    have hw : Ch11.wordState h 0 hN [m] = v := by
      rw [Ch11.word_state_cons, Ch11.word_state_nil, hsea]
    rw [← hw]
    simpa using sugawara_word_eigenvalue h hh 0 hN K M hM [m] (by simpa using hmK) (by simp only [abs_zero, add_zero]; exact_mod_cast hR2)
  refine ⟨v, hv, hnz, he, ?_⟩
  rw [he]
  exact smul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hm)) hnz

/-- The raising corollary has nonzero output on an admissible ground input. -/
lemma sugawara_commutator_witness (h : ℕ) (hh : 0 < h) (M n : ℕ)
    (hn : 0 < n) (hM : n ≤ M) (hR2 : 2*n ≤ h) :
    ∃ v : FockSpace h, v ∈ Ch07.fixedBudget h 0 0 ∧ v ≠ 0 ∧
      Ch09.rho h (n : ℤ) v ≠ 0 ∧
      A02.commutator (sugawaraHamiltonian h M) (Ch09.rho h (n : ℤ)) v ≠ 0 := by
  have hN : Ch07.admissible h 0 := by unfold Ch07.admissible; omega
  have hsea : Ch07.groundKet h 0 hN = Ch07.vacuumKet h := by
    unfold Ch07.groundKet Ch07.vacuumKet
    rw [Ch07.ground_configuration_zero]
    rfl
  have hv : Ch07.vacuumKet h ∈ Ch07.fixedBudget h 0 0 := by
    rw [← hsea]
    exact Ch07.ground_ket_mem_budget h hh 0 hN 0
  have hnz := Ch09.rho_sea_ne_zero h n hn (by omega)
  refine ⟨Ch07.vacuumKet h, hv, Ch07.vacuum_ket_ne_zero h, hnz, ?_⟩
  rw [sugawara_raising_commutator h hh 0 hN 0 M n (by simpa using hM) (by simp only [zero_add, abs_zero, add_zero]; exact_mod_cast hR2) _ hv]
  exact smul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hn)) hnz

end Bosonize.Ch12
