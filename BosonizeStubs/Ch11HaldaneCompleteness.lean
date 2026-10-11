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
    (partitionList p : Multiset ℕ) = p.parts := by
  simp [partitionList]

lemma partition_list_sum {E : ℕ} (p : Nat.Partition E) : (partitionList p).sum = E := by
  have he := congrArg Multiset.sum (partition_list_multiset p)
  simpa [p.parts_sum] using he

lemma partition_list_positive {E : ℕ} (p : Nat.Partition E) :
    ∀ m ∈ partitionList p, 0 < m := by
  intro m hm
  apply p.parts_pos
  simpa [← partition_list_multiset p] using hm

lemma creator_word_nil (h : ℕ) : creatorWord h [] = 1 := by
  simp [creatorWord]

lemma creator_word_cons (h m : ℕ) (parts : List ℕ) :
    creatorWord h (m::parts) = Ch09.rho h (m : ℤ) * creatorWord h parts := by
  simp [creatorWord]

lemma word_state_nil (h : ℕ) (N : ℤ) (hN : Ch07.admissible h N) :
    wordState h N hN [] = Ch07.groundKet h N hN := by
  simp [wordState, creator_word_nil]

lemma word_state_cons (h m : ℕ) (N : ℤ) (hN : Ch07.admissible h N) (parts : List ℕ) :
    wordState h N hN (m::parts) = Ch09.rho h (m : ℤ) (wordState h N hN parts) := by
  simp [wordState, creator_word_cons, Module.End.mul_apply]

lemma creator_word_perm (h : ℕ) (parts other : List ℕ) (hp : parts.Perm other) :
    creatorWord h parts = creatorWord h other := by
  unfold creatorWord
  simp only [bind_pure_comp]
  change ((parts.map (fun m : ℕ => (m : ℤ))).map (Ch09.rho h)).prod =
    ((other.map (fun m : ℕ => (m : ℤ))).map (Ch09.rho h)).prod
  simp only [List.map_map]
  apply List.Perm.prod_eq' (hp.map _)
  apply List.pairwise_map.mpr
  apply List.pairwise_of_forall
  intro m n
  exact sub_eq_zero.mp (Ch09.rho_positive_commute h (m : ℤ) (n : ℤ) (by omega) (by omega))

lemma partition_state_order_independent (h : ℕ) (N : ℤ) (hN : Ch07.admissible h N)
    {E : ℕ} (p : Nat.Partition E) (parts : List ℕ) (hp : (parts : Multiset ℕ) = p.parts) :
    wordState h N hN parts = partitionState h N hN p := by
  have hperm : parts.Perm (partitionList p) := by
    exact Quotient.exact (hp.trans (partition_list_multiset p).symm)
  change creatorWord h parts (Ch07.groundKet h N hN) = creatorWord h (partitionList p) (Ch07.groundKet h N hN)
  rw [creator_word_perm h parts (partitionList p) hperm]

lemma word_state_cons_erase (h m : ℕ) (N : ℤ) (hN : Ch07.admissible h N)
    (parts : List ℕ) (hm : m ∈ parts) :
    wordState h N hN parts = Ch09.rho h (m : ℤ) (wordState h N hN (parts.erase m)) := by
  rw [← word_state_cons]
  unfold wordState
  rw [creator_word_perm h parts (m::parts.erase m) (List.perm_cons_erase hm)]

lemma creator_word_exact_shift (h : ℕ) (parts : List ℕ) :
    A03.ExactShift (Ch07.relativeCharge h) (Ch07.excitationEnergy h)
      (creatorWord h parts) 0 (parts.sum : ℤ) := by
  induction parts with
  | nil =>
    intro S
    rw [creator_word_nil]
    apply (A03.ket_mem_coordinate_space _ _).mpr
    simp
  | cons m parts ih =>
    intro S
    rw [creator_word_cons, Module.End.mul_apply]
    have hword := ih S
    change creatorWord h parts (A02.ket S) ∈ A03.coordinateSpace _ at hword
    generalize hv : creatorWord h parts (A02.ket S) = v at hword ⊢
    clear hv
    induction hword using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨T, hT, rfl⟩ := hv
      change Ch07.relativeCharge h T = Ch07.relativeCharge h S + 0 ∧
        Ch07.excitationEnergy h T = Ch07.excitationEnergy h S + (parts.sum : ℤ) at hT
      apply A03.coordinate_space_mono _ _ (by
        intro U hU
        change Ch07.relativeCharge h U = Ch07.relativeCharge h T + 0 ∧
          Ch07.excitationEnergy h U = Ch07.excitationEnergy h T + (m : ℤ) at hU
        exact ⟨by omega, by simp only [List.sum_cons, Nat.cast_add]; omega⟩)
      exact Ch09.rho_exact_shift h (m : ℤ) T
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul a x _ hx => simpa using Submodule.smul_mem _ a hx

lemma word_state_mem_energy (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (parts : List ℕ) :
    wordState h N hN parts ∈ Ch07.energySpace h N (parts.sum : ℤ) := by
  have he := creator_word_exact_shift h parts (Ch07.groundConfiguration h N)
  apply A03.coordinate_space_mono _ _ (by
    intro T hT
    change Ch07.relativeCharge h T = Ch07.relativeCharge h (Ch07.groundConfiguration h N) + 0 ∧
      Ch07.excitationEnergy h T = Ch07.excitationEnergy h (Ch07.groundConfiguration h N) + (parts.sum : ℤ) at hT
    rw [Ch07.ground_configuration_charge h hh N hN,
      Ch07.ground_configuration_excitation h hh N hN] at hT
    simpa using hT)
  exact he

lemma word_state_mem_budget (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (parts : List ℕ) (K : ℕ) (hK : parts.sum ≤ K) :
    wordState h N hN parts ∈ Ch07.fixedBudget h N (K : ℤ) := by
  apply A03.coordinate_space_mono _ _ (by
    intro S hS
    change Ch07.relativeCharge h S = N ∧ Ch07.excitationEnergy h S = (parts.sum : ℤ) at hS
    exact ⟨hS.1, by omega⟩)
  exact word_state_mem_energy h hh N hN parts

lemma partition_state_mem_energy (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) {E : ℕ} (p : Nat.Partition E) :
    partitionState h N hN p ∈ Ch07.energySpace h N (E : ℤ) := by
  unfold partitionState
  simpa [partition_list_sum p] using word_state_mem_energy h hh N hN (partitionList p)

/-- Apply the CCR to the right remainder, which has budget exactly its sum. -/
lemma remainder_ccr (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : Ch07.admissible h N)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (parts : List ℕ)
    (hmargin : (m : ℤ)+(n : ℤ)+(parts.sum : ℤ)+|N| ≤ (h : ℤ)) :
    A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (n : ℤ))
      (wordState h N hN parts) =
        (if m=n then (m : ℂ) else 0) • wordState h N hN parts := by
  have hc := Ch10.rho_signed_ccr h hh (-(m : ℤ)) (n : ℤ) N (parts.sum : ℤ)
    (by simpa [abs_neg, abs_of_nonneg (by omega : 0≤(m : ℤ)), abs_of_nonneg (by omega : 0≤(n : ℤ))] using hmargin)
    (wordState h N hN parts) (word_state_mem_budget h hh N hN parts parts.sum le_rfl)
  have he : Ch10.schwingerCoefficient (-(m : ℤ)) (n : ℤ) = (if m=n then (m : ℂ) else 0) := by
    unfold Ch10.schwingerCoefficient
    by_cases hmn : m=n
    · simp [hmn]
    · have hi : -(m : ℤ)+(n : ℤ)≠0 := by omega
      simp [hmn, hi]
  simpa only [he] using hc

lemma right_remainder_margin (h K m n : ℕ) (N : ℤ) (parts : List ℕ)
    (hm : m ≤ K) (hn : n+parts.sum ≤ K)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    (m : ℤ)+(n : ℤ)+(parts.sum : ℤ)+|N| ≤ (h : ℤ) := by
  omega

/-- One actual pull-through step, with no restriction on the already traversed left prefix. -/
lemma lowering_cons (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : Ch07.admissible h N)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (parts : List ℕ)
    (hmargin : (m : ℤ)+(n : ℤ)+(parts.sum : ℤ)+|N| ≤ (h : ℤ)) :
    Ch09.rho h (-(m : ℤ)) (wordState h N hN (n::parts)) =
      Ch09.rho h (n : ℤ) (Ch09.rho h (-(m : ℤ)) (wordState h N hN parts)) +
        (if m=n then (m : ℂ) else 0) • wordState h N hN parts := by
  rw [word_state_cons]
  have hc := remainder_ccr h hh N hN m n hm hn parts hmargin
  change Ch09.rho h (-(m : ℤ)) (Ch09.rho h (n : ℤ) (wordState h N hN parts)) -
    Ch09.rho h (n : ℤ) (Ch09.rho h (-(m : ℤ)) (wordState h N hN parts)) = _ at hc
  simpa [add_comm] using (sub_eq_iff_eq_add.mp hc)

/-- Contract each matching occurrence; eraseIdx keeps occurrence multiplicity explicit. -/
lemma lowering_through_word (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K m : ℕ) (hm : 0 < m) (hmK : m ≤ K)
    (parts : List ℕ) (hpos : ∀ n ∈ parts, 0 < n) (hE : parts.sum ≤ K)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    Ch09.rho h (-(m : ℤ)) (wordState h N hN parts) =
      ∑ i : Fin parts.length,
        if parts[i] = m then (m : ℂ) • wordState h N hN (parts.eraseIdx i.val) else 0 := by
  induction parts with
  | nil =>
    simpa [word_state_nil] using Ch09.rho_lowering_ground h hh N hN (m : ℤ) (by omega)
  | cons n parts ih =>
    have hs : n+parts.sum≤K := by simpa using hE
    rw [lowering_cons h hh N hN m n hm (hpos n (by simp)) parts
      (right_remainder_margin h K m n N parts hmK hs hR2),
      ih (fun j hj => hpos j (by simp [hj])) (by omega)]
    by_cases hnm : n=m
    · subst n
      simp [Fin.sum_univ_succ, List.eraseIdx_cons_succ, word_state_cons, map_sum, apply_ite, add_comm]
    · simp [Fin.sum_univ_succ, List.eraseIdx_cons_succ, word_state_cons, map_sum, apply_ite, hnm, Ne.symm hnm, add_comm]

/-- Commutativity consolidates the occurrence sum into a count times one erased word. -/
lemma lowering_through_word_erase (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K m : ℕ) (hm : 0 < m) (hmK : m ≤ K)
    (parts : List ℕ) (hpos : ∀ n ∈ parts, 0 < n) (hE : parts.sum ≤ K)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    Ch09.rho h (-(m : ℤ)) (wordState h N hN parts) =
      (m*parts.count m : ℕ) • wordState h N hN (parts.erase m) := by
  have hc : Ch09.rho h (-(m : ℤ)) (wordState h N hN parts) =
      ((m : ℂ) * (parts.count m : ℂ)) • wordState h N hN (parts.erase m) := by
    induction parts with
    | nil => simpa [word_state_nil] using Ch09.rho_lowering_ground h hh N hN (m : ℤ) (by omega)
    | cons n parts ih =>
      have hs : n+parts.sum≤K := by simpa using hE
      rw [lowering_cons h hh N hN m n hm (hpos n (by simp)) parts
        (right_remainder_margin h K m n N parts hmK hs hR2),
        ih (fun j hj => hpos j (by simp [hj])) (by omega), map_smul]
      by_cases hmn : n=m
      · subst n
        simp only [List.erase_cons_head, List.count_cons_self, ite_true]
        by_cases hmem : m ∈ parts
        · rw [← word_state_cons_erase h m N hN parts hmem, ← add_smul]
          congr 1
          push_cast
          ring
        · have hz : parts.count m=0 := List.count_eq_zero.mpr hmem
          simp [hz]
      · have hmn' : m≠n := Ne.symm hmn
        simp only [hmn', ite_false, zero_smul, add_zero]
        have her : (n::parts).erase m=n::parts.erase m := List.erase_cons_tail (by simp [hmn])
        simp only [List.count_cons, beq_iff_eq, hmn, ite_false, Nat.add_zero, her, word_state_cons]
  rw [← Nat.cast_smul_eq_nsmul (R := ℂ)]
  simpa only [Nat.cast_mul] using hc

lemma word_inner_cons (h : ℕ) (N : ℤ) (hN : Ch07.admissible h N)
    (m : ℕ) (left right : List ℕ) :
    inner ℂ (wordState h N hN (m::left)) (wordState h N hN right) =
      inner ℂ (wordState h N hN left)
        (Ch09.rho h (-(m : ℤ)) (wordState h N hN right)) := by
  rw [word_state_cons]
  have hi := LinearMap.adjoint_inner_left (Ch09.rho h (-(m : ℤ)))
    (wordState h N hN right) (wordState h N hN left)
  simpa [Ch09.rho_adjoint] using hi

lemma ground_inner_word_zero (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (parts : List ℕ) (hE : 0 < parts.sum) :
    inner ℂ (Ch07.groundKet h N hN) (wordState h N hN parts) = 0 := by
  apply A03.energy_spaces_orthogonal (Ch07.relativeCharge h) (Ch07.excitationEnergy h)
    N 0 N (parts.sum : ℤ) (Or.inr (by omega))
  · apply (A03.ket_mem_coordinate_space _ _).mpr
    exact ⟨Ch07.ground_configuration_charge h hh N hN, Ch07.ground_configuration_excitation h hh N hN⟩
  · exact word_state_mem_energy h hh N hN parts

lemma ground_inner_ground (h : ℕ) (N : ℤ) (hN : Ch07.admissible h N) :
    inner ℂ (Ch07.groundKet h N hN) (Ch07.groundKet h N hN) = 1 := by
  change inner ℂ (A02.ket (Ch07.groundConfiguration h N)) (A02.ket (Ch07.groundConfiguration h N)) = 1
  rw [A02.ket_inner]
  simp

lemma hall_factor_positive (parts : Multiset ℕ) (hpos : ∀ m ∈ parts, 0 < m) :
    0 < hallFactor parts := by
  unfold hallFactor
  apply Finset.prod_pos
  intro m hm
  exact Nat.mul_pos (Nat.pow_pos (hpos m (by simpa using hm))) (Nat.factorial_pos _)

lemma hall_factor_cons (m : ℕ) (hm : 0 < m) (parts : Multiset ℕ)
    (hpos : ∀ n ∈ parts, 0 < n) :
    hallFactor (m ::ₘ parts) = m*(parts.count m+1)*hallFactor parts := by
  have hpositive : 0 < hallFactor (m::ₘ parts) := hall_factor_positive _ (by
    intro n hn
    rcases Multiset.mem_cons.mp hn with he | he
    · simpa [he] using hm
    · exact hpos n he)
  apply Nat.eq_of_mul_eq_mul_left hpositive
  have hsplit (xs : Multiset ℕ) : hallFactor xs = m^(xs.count m)*(xs.count m).factorial *
      ∏ n ∈ xs.toFinset.erase m, n^(xs.count n)*(xs.count n).factorial := by
    unfold hallFactor
    by_cases hmem : m ∈ xs.toFinset
    · exact (Finset.mul_prod_erase _ _ hmem).symm
    · have hz : xs.count m=0 := Multiset.count_eq_zero.mpr (by simpa using hmem)
      simp [hz, Finset.erase_eq_of_notMem hmem]
  rw [hsplit (m::ₘ parts), hsplit parts]
  have he : (m::ₘ parts).toFinset.erase m=parts.toFinset.erase m := by simp
  rw [he]
  have hp : (∏ n ∈ parts.toFinset.erase m, n^((m::ₘ parts).count n)*((m::ₘ parts).count n).factorial) =
      ∏ n ∈ parts.toFinset.erase m, n^(parts.count n)*(parts.count n).factorial := by
    apply Finset.prod_congr rfl
    intro n hn
    have hn' : m≠n := (Finset.mem_erase.mp hn).1.symm
    rw [Multiset.count_cons_of_ne hn'.symm]
  rw [hp, Multiset.count_cons_self, pow_succ, Nat.factorial_succ]
  ring

lemma word_gram (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : Ch07.admissible h N)
    (K : ℕ) (left right : List ℕ)
    (hl : ∀ m ∈ left, 0 < m) (hr : ∀ m ∈ right, 0 < m)
    (hlK : left.sum ≤ K) (hrK : right.sum ≤ K)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    inner ℂ (wordState h N hN left) (wordState h N hN right) =
      if (left : Multiset ℕ) = (right : Multiset ℕ)
      then (hallFactor (left : Multiset ℕ) : ℂ) else 0 := by
  classical
  have hgram (xs ys : List ℕ) (hxpos : ∀ m ∈ xs, 0<m) (hypos : ∀ m ∈ ys, 0<m)
      (hx : xs.sum≤K) (hy : ys.sum≤K) :
      inner ℂ (wordState h N hN xs) (wordState h N hN ys) =
        if xs.Perm ys then (hallFactor (xs : Multiset ℕ) : ℂ) else 0 := by
    induction xs generalizing ys with
    | nil =>
      cases ys with
      | nil => simpa [word_state_nil, hallFactor] using ground_inner_ground h N hN
      | cons m ys =>
        have hs : 0<(m::ys).sum := by have hm := hypos m (by simp); simp only [List.sum_cons]; omega
        simpa [word_state_nil] using ground_inner_word_zero h hh N hN (m::ys) hs
    | cons m xs ih =>
      have hs : m+xs.sum≤K := by simpa using hx
      rw [word_inner_cons, lowering_through_word_erase h hh N hN K m
        (hxpos m (by simp)) (by omega) ys hypos hy hR2,
        ← Nat.cast_smul_eq_nsmul (R := ℂ), inner_smul_right, Nat.cast_mul]
      by_cases hmem : m ∈ ys
      · have herpos : ∀ n ∈ ys.erase m, 0<n := fun n hn => hypos n (List.mem_of_mem_erase hn)
        have hsum : m+(ys.erase m).sum=ys.sum := by simpa using (List.perm_cons_erase hmem).sum_eq.symm
        rw [ih (ys.erase m) (fun n hn => hxpos n (by simp [hn])) herpos (by omega) (by omega)]
        have hequiv : (m::xs).Perm ys ↔ xs.Perm (ys.erase m) := by
          constructor
          · intro hp
            exact (hp.trans (List.perm_cons_erase hmem)).cons_inv
          · intro hp
            exact (hp.cons m).trans (List.perm_cons_erase hmem).symm
        by_cases hp : xs.Perm (ys.erase m)
        · have hp' := hequiv.mpr hp
          have hc := hp'.count_eq m
          simp only [List.count_cons_self] at hc
          simp only [hp, hp', ite_true, ← hc]
          rw [show hallFactor ((m::xs : List ℕ) : Multiset ℕ) =
              m*(xs.count m+1)*hallFactor (xs : Multiset ℕ) from
            by
              simpa only [Multiset.cons_coe, Multiset.coe_count] using
                hall_factor_cons m (hxpos m (by simp)) (xs : Multiset ℕ)
                  (fun n hn => hxpos n (List.mem_cons_of_mem m (show n ∈ xs from hn)))]
          simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        · have hp' : ¬(m::xs).Perm ys := fun h => hp (hequiv.mp h)
          simp [hp, hp']
      · have hc : ys.count m=0 := List.count_eq_zero.mpr hmem
        have hp' : ¬(m::xs).Perm ys := by
          intro hp
          exact hmem (hp.mem_iff.mp (by simp))
        simp [hc, hp']
  simpa only [Multiset.coe_eq_coe] using hgram left right hl hr hlK hrK

theorem partition_gram (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : Ch07.admissible h N)
    (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) (p q : Nat.Partition K) :
    inner ℂ (partitionState h N hN p) (partitionState h N hN q) =
      if p=q then (partitionNormalization p : ℂ) else 0 := by
  have hg := word_gram h hh N hN K (partitionList p) (partitionList q)
    (partition_list_positive p) (partition_list_positive q)
    (by rw [partition_list_sum]) (by rw [partition_list_sum]) hR2
  have he : p.parts=q.parts ↔ p=q := ⟨Nat.Partition.ext, fun hp => congrArg Nat.Partition.parts hp⟩
  simpa only [partitionState, partition_list_multiset, he, partitionNormalization] using hg

lemma partition_state_ne_zero (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ))
    (p : Nat.Partition K) : partitionState h N hN p ≠ 0 := by
  intro hz
  have hg := partition_gram h hh N hN K hR2 p p
  have hn : (partitionNormalization p : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hall_factor_positive p.parts (fun m hm => p.parts_pos hm)))
  simp only [hz, inner_zero_left] at hg
  exact hn hg.symm

lemma partition_states_linear_independent (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    LinearIndependent ℂ (partitionState h N hN (E := K)) := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · exact partition_state_ne_zero h hh N hN K hR2
  · intro p q hpq
    rw [partition_gram h hh N hN K hR2 p q, ite_eq_right_iff.mpr (fun he => (hpq he).elim)]

lemma r2_implies_r1 (h K : ℕ) (N : ℤ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    (K : ℤ) ≤ min ((h : ℤ)+N) ((h : ℤ)-N) := by
  have h1 := le_abs_self N
  have h2 := neg_le_abs N
  rw [le_min_iff]
  constructor <;> omega

theorem fixed_energy_spanning (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    Submodule.span ℂ (Set.range (partitionState h N hN (E := K))) =
      Ch07.energySpace h N (K : ℤ) := by
  let v : Nat.Partition K → Ch07.energySpace h N (K : ℤ) :=
    fun p => ⟨partitionState h N hN p, partition_state_mem_energy h hh N hN p⟩
  have hv : LinearIndependent ℂ v :=
    (partition_states_linear_independent h hh N hN K hR2).of_comp
      (Ch07.energySpace h N (K : ℤ)).subtype
  have hs := hv.span_eq_top_of_card_eq_finrank' (by
    exact (A04Partitions.energy_space_finrank_r1 h hh N hN K (r2_implies_r1 h K N hR2)).symm)
  exact (Submodule.span_range_subtype_eq_top_iff _
    (fun p => partition_state_mem_energy h hh N hN p)).mp hs

theorem fixed_energy_basis (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    ∃ b : Module.Basis (Nat.Partition K) ℂ (Ch07.energySpace h N (K : ℤ)),
      ∀ p, (b p : Ch07.FockSpace h) = partitionState h N hN p := by
  let v : Nat.Partition K → Ch07.energySpace h N (K : ℤ) :=
    fun p => ⟨partitionState h N hN p, partition_state_mem_energy h hh N hN p⟩
  have hv : LinearIndependent ℂ v :=
    (partition_states_linear_independent h hh N hN K hR2).of_comp
      (Ch07.energySpace h N (K : ℤ)).subtype
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' v hv ?_, ?_⟩
  · exact (A04Partitions.energy_space_finrank_r1 h hh N hN K (r2_implies_r1 h K N hR2)).symm
  · intro p
    change ((basisOfLinearIndependentOfCardEqFinrank' v hv _) p).val = _
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']

lemma budget_partition_gram (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ))
    (p q : BudgetPartitions K) :
    inner ℂ (budgetPartitionState h N hN p) (budgetPartitionState h N hN q) =
      if p=q then (partitionNormalization p.2 : ℂ) else 0 := by
  have hpK : p.1.val ≤ K := Nat.le_of_lt_succ p.1.isLt
  have hqK : q.1.val ≤ K := Nat.le_of_lt_succ q.1.isLt
  have hg := word_gram h hh N hN K (partitionList p.2) (partitionList q.2)
    (partition_list_positive p.2) (partition_list_positive q.2)
    (by simpa only [partition_list_sum] using hpK)
    (by simpa only [partition_list_sum] using hqK) hR2
  have he : p.2.parts = q.2.parts ↔ p = q := by
    constructor
    · intro hparts
      rcases p with ⟨⟨ep, hep⟩, pp⟩
      rcases q with ⟨⟨eq, heq⟩, qq⟩
      have hE : ep = eq := by
        simpa only [pp.parts_sum, qq.parts_sum] using congrArg Multiset.sum hparts
      subst eq
      have ht : pp = qq := Nat.Partition.ext hparts
      subst qq
      rfl
    · rintro rfl
      rfl
  simpa only [partition_list_multiset, he, partitionNormalization,
    budgetPartitionState, partitionState] using hg

lemma budget_partition_mem (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (p : BudgetPartitions K) :
    budgetPartitionState h N hN p ∈ Ch07.fixedBudget h N (K : ℤ) := by
  apply word_state_mem_budget h hh N hN (partitionList p.2) K
  rw [partition_list_sum]
  exact Nat.le_of_lt_succ p.1.isLt

lemma budget_partition_linear_independent (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    LinearIndependent ℂ (budgetPartitionState h N hN (K := K)) := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · intro p
    exact partition_state_ne_zero h hh N hN p.1.val
      (by have := Nat.le_of_lt_succ p.1.isLt; omega) p.2
  · intro p q hpq
    rw [budget_partition_gram h hh N hN K hR2 p q,
      ite_eq_right_iff.mpr (fun he => (hpq he).elim)]

theorem budget_partition_spanning (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    Submodule.span ℂ (Set.range (budgetPartitionState h N hN (K := K))) =
      Ch07.fixedBudget h N (K : ℤ) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact budget_partition_mem h hh N hN K p
  · change Submodule.span ℂ (A02.ket '' {S | Ch07.relativeCharge h S = N ∧
      Ch07.excitationEnergy h S ≤ (K : ℤ)}) ≤ _
    apply Submodule.span_le.mpr
    rintro _ ⟨S, ⟨hSN, hSK⟩, rfl⟩
    let E := (Ch07.excitationEnergy h S).toNat
    have hE : (E : ℤ) = Ch07.excitationEnergy h S :=
      Int.toNat_of_nonneg (Ch07.excitation_nonneg h hh S)
    have hEK : E ≤ K := by omega
    have hm : A02.ket S ∈ Ch07.energySpace h N (E : ℤ) := by
      apply (A03.ket_mem_coordinate_space _ _).mpr
      exact ⟨hSN, hE.symm⟩
    rw [← fixed_energy_spanning h hh N hN E (by omega)] at hm
    apply (Submodule.span_mono ?_) hm
    rintro _ ⟨p, rfl⟩
    exact ⟨⟨⟨E, by omega⟩, p⟩, rfl⟩

theorem budget_partition_basis (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    ∃ b : Module.Basis (BudgetPartitions K) ℂ (Ch07.fixedBudget h N (K : ℤ)),
      ∀ p, (b p : Ch07.FockSpace h) = budgetPartitionState h N hN p := by
  let v : BudgetPartitions K → Ch07.fixedBudget h N (K : ℤ) :=
    fun p => ⟨budgetPartitionState h N hN p, budget_partition_mem h hh N hN K p⟩
  have hv : LinearIndependent ℂ v :=
    (budget_partition_linear_independent h hh N hN K hR2).of_comp
      (Ch07.fixedBudget h N (K : ℤ)).subtype
  have hs : Submodule.span ℂ (Set.range v) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff _
      (fun p => budget_partition_mem h hh N hN K p)).mpr
        (budget_partition_spanning h hh N hN K hR2)
  refine ⟨Module.Basis.mk hv hs.ge, ?_⟩
  intro p
  rw [Module.Basis.coe_mk]

end Bosonize.Ch11
