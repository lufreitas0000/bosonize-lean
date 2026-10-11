module

public import Bosonize.Core.Ch10Heisenberg
public import BosonizeStubs.A04PartitionCombinatorics

@[expose] public section
namespace Bosonize.Ch11
open scoped BigOperators Classical

/-- Written order: the rightmost current acts first. -/
noncomputable def creatorWord (h : ℕ) (parts : List ℕ) : Ch09.Operators h :=
  (parts.map fun m => Ch09.rho h (m : ℤ)).prod

noncomputable def wordState (h : ℕ) (N : ℤ) (hN : Ch07.admissible h N)
    (parts : List ℕ) : Ch07.FockSpace h := creatorWord h parts (Ch07.groundKet h N hN)

def partitionList {E : ℕ} (p : Nat.Partition E) : List ℕ := p.parts.sort (· ≥ ·)

noncomputable def partitionState (h : ℕ) (N : ℤ) (hN : Ch07.admissible h N)
    {E : ℕ} (p : Nat.Partition E) : Ch07.FockSpace h := wordState h N hN (partitionList p)

def hallFactor (parts : Multiset ℕ) : ℕ :=
  ∏ m ∈ parts.toFinset, m ^ parts.count m * (parts.count m).factorial

def partitionNormalization {E : ℕ} (p : Nat.Partition E) : ℕ := hallFactor p.parts

abbrev BudgetPartitions (K : ℕ) := (E : Fin (K+1)) × Nat.Partition E.val

noncomputable def budgetPartitionState (h : ℕ) (N : ℤ) (hN : Ch07.admissible h N)
    {K : ℕ} (p : BudgetPartitions K) : Ch07.FockSpace h := partitionState h N hN p.2

lemma partition_list_multiset {E : ℕ} (p : Nat.Partition E) :
    (partitionList p : Multiset ℕ) = p.parts := by sorry

lemma partition_list_sum {E : ℕ} (p : Nat.Partition E) : (partitionList p).sum = E := by sorry

lemma partition_list_positive {E : ℕ} (p : Nat.Partition E) :
    ∀ m ∈ partitionList p, 0 < m := by sorry

lemma creator_word_nil (h : ℕ) : creatorWord h [] = 1 := by sorry

lemma creator_word_cons (h m : ℕ) (parts : List ℕ) :
    creatorWord h (m::parts) = Ch09.rho h (m : ℤ) * creatorWord h parts := by sorry

lemma word_state_nil (h : ℕ) (N : ℤ) (hN : Ch07.admissible h N) :
    wordState h N hN [] = Ch07.groundKet h N hN := by sorry

lemma word_state_cons (h m : ℕ) (N : ℤ) (hN : Ch07.admissible h N) (parts : List ℕ) :
    wordState h N hN (m::parts) = Ch09.rho h (m : ℤ) (wordState h N hN parts) := by sorry

lemma creator_word_perm (h : ℕ) (parts other : List ℕ) (hp : parts.Perm other) :
    creatorWord h parts = creatorWord h other := by sorry

lemma partition_state_order_independent (h : ℕ) (N : ℤ) (hN : Ch07.admissible h N)
    {E : ℕ} (p : Nat.Partition E) (parts : List ℕ) (hp : (parts : Multiset ℕ) = p.parts) :
    wordState h N hN parts = partitionState h N hN p := by sorry

lemma word_state_cons_erase (h m : ℕ) (N : ℤ) (hN : Ch07.admissible h N)
    (parts : List ℕ) (hm : m ∈ parts) :
    wordState h N hN parts = Ch09.rho h (m : ℤ) (wordState h N hN (parts.erase m)) := by sorry

lemma creator_word_exact_shift (h : ℕ) (parts : List ℕ) :
    A03.ExactShift (Ch07.relativeCharge h) (Ch07.excitationEnergy h)
      (creatorWord h parts) 0 (parts.sum : ℤ) := by sorry

lemma word_state_mem_energy (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (parts : List ℕ) :
    wordState h N hN parts ∈ Ch07.energySpace h N (parts.sum : ℤ) := by sorry

lemma word_state_mem_budget (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (parts : List ℕ) (K : ℕ) (hK : parts.sum ≤ K) :
    wordState h N hN parts ∈ Ch07.fixedBudget h N (K : ℤ) := by sorry

lemma partition_state_mem_energy (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) {E : ℕ} (p : Nat.Partition E) :
    partitionState h N hN p ∈ Ch07.energySpace h N (E : ℤ) := by sorry

/-- Apply the CCR to the right remainder, which has budget exactly its sum. -/
lemma remainder_ccr (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : Ch07.admissible h N)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (parts : List ℕ)
    (hmargin : (m : ℤ)+(n : ℤ)+(parts.sum : ℤ)+|N| ≤ (h : ℤ)) :
    A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (n : ℤ))
      (wordState h N hN parts) =
        (if m=n then (m : ℂ) else 0) • wordState h N hN parts := by sorry

lemma right_remainder_margin (h K m n : ℕ) (N : ℤ) (parts : List ℕ)
    (hm : m ≤ K) (hn : n+parts.sum ≤ K)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    (m : ℤ)+(n : ℤ)+(parts.sum : ℤ)+|N| ≤ (h : ℤ) := by sorry

/-- One actual pull-through step, with no restriction on the already traversed left prefix. -/
lemma lowering_cons (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : Ch07.admissible h N)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (parts : List ℕ)
    (hmargin : (m : ℤ)+(n : ℤ)+(parts.sum : ℤ)+|N| ≤ (h : ℤ)) :
    Ch09.rho h (-(m : ℤ)) (wordState h N hN (n::parts)) =
      Ch09.rho h (n : ℤ) (Ch09.rho h (-(m : ℤ)) (wordState h N hN parts)) +
        (if m=n then (m : ℂ) else 0) • wordState h N hN parts := by sorry

/-- Contract each matching occurrence; eraseIdx keeps occurrence multiplicity explicit. -/
lemma lowering_through_word (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K m : ℕ) (hm : 0 < m) (hmK : m ≤ K)
    (parts : List ℕ) (hpos : ∀ n ∈ parts, 0 < n) (hE : parts.sum ≤ K)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    Ch09.rho h (-(m : ℤ)) (wordState h N hN parts) =
      ∑ i : Fin parts.length,
        if parts[i] = m then (m : ℂ) • wordState h N hN (parts.eraseIdx i.val) else 0 := by sorry

/-- Commutativity consolidates the occurrence sum into a count times one erased word. -/
lemma lowering_through_word_erase (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K m : ℕ) (hm : 0 < m) (hmK : m ≤ K)
    (parts : List ℕ) (hpos : ∀ n ∈ parts, 0 < n) (hE : parts.sum ≤ K)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    Ch09.rho h (-(m : ℤ)) (wordState h N hN parts) =
      (m*parts.count m : ℕ) • wordState h N hN (parts.erase m) := by sorry

lemma word_inner_cons (h : ℕ) (N : ℤ) (hN : Ch07.admissible h N)
    (m : ℕ) (left right : List ℕ) :
    inner ℂ (wordState h N hN (m::left)) (wordState h N hN right) =
      inner ℂ (wordState h N hN left)
        (Ch09.rho h (-(m : ℤ)) (wordState h N hN right)) := by sorry

lemma ground_inner_word_zero (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (parts : List ℕ) (hE : 0 < parts.sum) :
    inner ℂ (Ch07.groundKet h N hN) (wordState h N hN parts) = 0 := by sorry

lemma ground_inner_ground (h : ℕ) (N : ℤ) (hN : Ch07.admissible h N) :
    inner ℂ (Ch07.groundKet h N hN) (Ch07.groundKet h N hN) = 1 := by sorry

lemma hall_factor_positive (parts : Multiset ℕ) (hpos : ∀ m ∈ parts, 0 < m) :
    0 < hallFactor parts := by sorry

lemma hall_factor_cons (m : ℕ) (hm : 0 < m) (parts : Multiset ℕ)
    (hpos : ∀ n ∈ parts, 0 < n) :
    hallFactor (m ::ₘ parts) = m*(parts.count m+1)*hallFactor parts := by sorry

lemma word_gram (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : Ch07.admissible h N)
    (K : ℕ) (left right : List ℕ)
    (hl : ∀ m ∈ left, 0 < m) (hr : ∀ m ∈ right, 0 < m)
    (hlK : left.sum ≤ K) (hrK : right.sum ≤ K)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    inner ℂ (wordState h N hN left) (wordState h N hN right) =
      if (left : Multiset ℕ) = (right : Multiset ℕ)
      then (hallFactor (left : Multiset ℕ) : ℂ) else 0 := by sorry

theorem partition_gram (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : Ch07.admissible h N)
    (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) (p q : Nat.Partition K) :
    inner ℂ (partitionState h N hN p) (partitionState h N hN q) =
      if p=q then (partitionNormalization p : ℂ) else 0 := by sorry

lemma partition_state_ne_zero (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ))
    (p : Nat.Partition K) : partitionState h N hN p ≠ 0 := by sorry

lemma partition_states_linear_independent (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    LinearIndependent ℂ (partitionState h N hN (E := K)) := by sorry

lemma r2_implies_r1 (h K : ℕ) (N : ℤ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    (K : ℤ) ≤ min ((h : ℤ)+N) ((h : ℤ)-N) := by sorry

theorem fixed_energy_spanning (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    Submodule.span ℂ (Set.range (partitionState h N hN (E := K))) =
      Ch07.energySpace h N (K : ℤ) := by sorry

theorem fixed_energy_basis (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    ∃ b : Module.Basis (Nat.Partition K) ℂ (Ch07.energySpace h N (K : ℤ)),
      ∀ p, (b p : Ch07.FockSpace h) = partitionState h N hN p := by sorry

lemma budget_partition_gram (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ))
    (p q : BudgetPartitions K) :
    inner ℂ (budgetPartitionState h N hN p) (budgetPartitionState h N hN q) =
      if p=q then (partitionNormalization p.2 : ℂ) else 0 := by sorry

lemma budget_partition_mem (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (p : BudgetPartitions K) :
    budgetPartitionState h N hN p ∈ Ch07.fixedBudget h N (K : ℤ) := by sorry

lemma budget_partition_linear_independent (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    LinearIndependent ℂ (budgetPartitionState h N hN (K := K)) := by sorry

theorem budget_partition_spanning (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    Submodule.span ℂ (Set.range (budgetPartitionState h N hN (K := K))) =
      Ch07.fixedBudget h N (K : ℤ) := by sorry

theorem budget_partition_basis (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    ∃ b : Module.Basis (BudgetPartitions K) ℂ (Ch07.fixedBudget h N (K : ℤ)),
      ∀ p, (b p : Ch07.FockSpace h) = budgetPartitionState h N hN p := by sorry

end Bosonize.Ch11
