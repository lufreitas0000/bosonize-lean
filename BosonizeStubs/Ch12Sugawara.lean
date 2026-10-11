module

public import Bosonize.Core.Ch11HaldaneCompleteness

/-! Phase A: actual finite Sugawara operator and exact budget action.
The positive current is on the left; the lowering current acts first.
All theorem bodies are staging contracts, not established results. -/
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

lemma sugawara_zero (h : ℕ) : sugawaraHamiltonian h 0 = 0 := by sorry

lemma sugawara_apply (h M : ℕ) (v : FockSpace h) :
    sugawaraHamiltonian h M v =
      ∑ m ∈ Finset.Icc 1 M, Ch09.rho h (m : ℤ) (Ch09.rho h (-(m : ℤ)) v) := by sorry

lemma sugawara_adjoint (h M : ℕ) :
    LinearMap.adjoint (sugawaraHamiltonian h M) = sugawaraHamiltonian h M := by sorry

/-- A genuinely positive quadratic form on the ambient concrete Hilbert carrier. -/
lemma sugawara_inner (h M : ℕ) (v : FockSpace h) :
    inner ℂ v (sugawaraHamiltonian h M v) =
      ∑ m ∈ Finset.Icc 1 M, inner ℂ (Ch09.rho h (-(m : ℤ)) v)
        (Ch09.rho h (-(m : ℤ)) v) := by sorry

lemma sugawara_ground (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (M : ℕ) :
    sugawaraHamiltonian h M (Ch07.groundKet h N hN) = 0 := by sorry

/-- Grading removes these terms before any current pull-through is attempted. -/
lemma inactive_mode_zero (h : ℕ) (hh : 0 < h) (N : ℤ) (K m : ℕ)
    (hm : K < m) (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    (Ch09.rho h (m : ℤ) * Ch09.rho h (-(m : ℤ))) v = 0 := by sorry

/-- Cutoff stability requires no R2 margin and no upper bound on M. -/
lemma sugawara_cutoff_budget (h : ℕ) (hh : 0 < h) (N : ℤ) (K M : ℕ)
    (hM : K ≤ M) (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    sugawaraHamiltonian h M v = sugawaraHamiltonian h K v := by sorry

lemma sugawara_cutoff_independent (h : ℕ) (hh : 0 < h) (N : ℤ) (K M M' : ℕ)
    (hM : K ≤ M) (hM' : K ≤ M') (v : FockSpace h)
    (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    sugawaraHamiltonian h M v = sugawaraHamiltonian h M' v := by sorry

/-- Restore each erased occurrence using globally commuting positive modes.
The count can be zero; there is no spurious membership assumption on m. -/
lemma density_bilinear_word (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K m : ℕ) (hm : 0 < m) (hmK : m ≤ K)
    (parts : List ℕ) (hE : parts.sum ≤ K)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    (Ch09.rho h (m : ℤ) * Ch09.rho h (-(m : ℤ))) (Ch11.wordState h N hN parts) =
      ((m*parts.count m : ℕ) : ℂ) • Ch11.wordState h N hN parts := by sorry

lemma positive_word_weight (K : ℕ) (parts : List ℕ)
    (hE : parts.sum ≤ K) :
    ∑ m ∈ Finset.Icc 1 K, m*parts.count m = parts.sum := by sorry

lemma sugawara_word_eigenvalue (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M : ℕ) (hM : K ≤ M)
    (parts : List ℕ) (hE : parts.sum ≤ K)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    sugawaraHamiltonian h M (Ch11.wordState h N hN parts) =
      (parts.sum : ℂ) • Ch11.wordState h N hN parts := by sorry

lemma sugawara_partition_eigenvalue (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M E : ℕ) (hEK : E ≤ K) (hM : K ≤ M)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) (p : Nat.Partition E) :
    sugawaraHamiltonian h M (Ch11.partitionState h N hN p) =
      (E : ℂ) • Ch11.partitionState h N hN p := by sorry

lemma excitation_energy_space (h : ℕ) (N E : ℤ) (v : FockSpace h)
    (hv : v ∈ Ch07.energySpace h N E) :
    Ch07.excitationObservable h v = (E : ℂ) • v := by sorry

lemma excitation_partition_eigenvalue (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (E : ℕ) (p : Nat.Partition E) :
    Ch07.excitationObservable h (Ch11.partitionState h N hN p) =
      (E : ℂ) • Ch11.partitionState h N hN p := by sorry

lemma sugawara_budget_partition_eigenvalue (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M : ℕ) (hM : K ≤ M)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) (p : Ch11.BudgetPartitions K) :
    sugawaraHamiltonian h M (Ch11.budgetPartitionState h N hN p) =
      (p.1.val : ℂ) • Ch11.budgetPartitionState h N hN p := by sorry

/-- Extend equality across the whole actual CH11 partition basis. -/
theorem sugawara_equivalence (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M : ℕ) (hM : K ≤ M)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ))
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    Ch07.excitationObservable h v = sugawaraHamiltonian h M v := by sorry

lemma relative_energy_budget (h : ℕ) (N : ℤ) (K : ℕ)
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    Ch05.shiftedHamiltonian (2*h) v =
      Ch07.excitationObservable h v + (Ch07.groundEnergy N : ℂ) • v := by sorry

lemma ground_energy_complex (N : ℤ) :
    (Ch07.groundEnergy N : ℂ) = (N : ℂ)*((N : ℂ)+1)/2 := by sorry

/-- Same-sea integer ground shift is N(N+1)/2, including negative charges. -/
theorem sugawara_relative_hamiltonian (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M : ℕ) (hM : K ≤ M)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ))
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    Ch05.shiftedHamiltonian (2*h) v =
      (sugawaraHamiltonian h M + ((N : ℂ)*((N : ℂ)+1)/2) • 1) v := by sorry

/-- Signed action with separate source and target margins. The target may be any
nonnegative bound dominating the actual signed energy shift K+n. -/
theorem sugawara_signed_commutator (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K J M : ℕ) (n : ℤ)
    (hshift : (K : ℤ)+n ≤ (J : ℤ)) (hMK : K ≤ M) (hMJ : J ≤ M)
    (hsource : 2*(K : ℤ)+|N| ≤ (h : ℤ))
    (htarget : 2*(J : ℤ)+|N| ≤ (h : ℤ))
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    A02.commutator (sugawaraHamiltonian h M) (Ch09.rho h n) v =
      (n : ℂ) • Ch09.rho h n v := by sorry

/-- Nonnegative transfer uses the actual enlarged target K+n.
CH12's n>0 corollary is its positive special case; n=0 is also valid. -/
theorem sugawara_raising_commutator (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M n : ℕ)
    (hM : K+n ≤ M) (hR2 : 2*((K+n : ℕ) : ℤ)+|N| ≤ (h : ℤ))
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    A02.commutator (sugawaraHamiltonian h M) (Ch09.rho h (n : ℤ)) v =
      (n : ℂ) • Ch09.rho h (n : ℤ) v := by sorry

lemma physical_relative_budget (h : ℕ) (hh : 0 < h) (β : ℝ) (N : ℤ) (K : ℕ)
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    physicalRelativeHamiltonian h β v = Ch05.shiftedHamiltonian (2*h) v +
      ((β : ℂ)*(N : ℂ)) • v := by sorry

/-- Cancellation concerns excitation after subtracting the matching ground
polynomial; neither bare nor relative physical energy is twist independent. -/
lemma physical_excitation_cancel (h : ℕ) (hh : 0 < h) (β : ℝ) :
    physicalExcitationObservable h β = Ch07.excitationObservable h := by sorry

theorem physical_sugawara_budget (h : ℕ) (hh : 0 < h) (β : ℝ) (N : ℤ)
    (hN : Ch07.admissible h N) (K M : ℕ) (hM : K ≤ M)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ))
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    physicalRelativeHamiltonian h β v = sugawaraHamiltonian h M v +
      (Ch06Ext.physicalGroundEnergy β N : ℂ) • v := by sorry

/-- An actual excited vector, not only nonemptiness of the budget. -/
lemma sugawara_excited_witness (h : ℕ) (hh : 0 < h) (K M m : ℕ)
    (hm : 0 < m) (hmK : m ≤ K) (hM : K ≤ M) (hR2 : 2*K ≤ h) :
    ∃ v : FockSpace h, v ∈ Ch07.fixedBudget h 0 (K : ℤ) ∧ v ≠ 0 ∧
      sugawaraHamiltonian h M v = (m : ℂ) • v ∧ sugawaraHamiltonian h M v ≠ 0 := by sorry

/-- The raising corollary has nonzero output on an admissible ground input. -/
lemma sugawara_commutator_witness (h : ℕ) (hh : 0 < h) (M n : ℕ)
    (hn : 0 < n) (hM : n ≤ M) (hR2 : 2*n ≤ h) :
    ∃ v : FockSpace h, v ∈ Ch07.fixedBudget h 0 0 ∧ v ≠ 0 ∧
      Ch09.rho h (n : ℤ) v ≠ 0 ∧
      A02.commutator (sugawaraHamiltonian h M) (Ch09.rho h (n : ℤ)) v ≠ 0 := by sorry

end Bosonize.Ch12
