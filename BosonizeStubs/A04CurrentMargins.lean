module
public import Bosonize.Core.Ch09DensityModes
/-! # A04 restricted current support
Phase A. Concrete frozen-occupation action and finite edge sums, not abstract CCR.
-/
@[expose] public section
namespace Bosonize.A04
open scoped BigOperators Classical

/-- The bottom m modes of the signed even band; the filter uses integer endpoints. -/
def bottomEdge (h m : ℕ) : Finset (Ch01.Band (2*h)) :=
  Finset.univ.filter (fun k => k.val ≤ -(h : ℤ)+(m : ℤ))

/-- The top m modes, with strict lower endpoint h-m and inclusive upper endpoint h. -/
def topEdge (h m : ℕ) : Finset (Ch01.Band (2*h)) :=
  Finset.univ.filter (fun k => (h : ℤ)-(m : ℤ) < k.val)

/-- The exact bottom occupation minus top occupation operator on the full Fock space. -/
noncomputable def diagonalEdge (h m : ℕ) : Ch09.Operators h :=
  (∑ k ∈ bottomEdge h m, Ch04.number k) - (∑ k ∈ topEdge h m, Ch04.number k)

/-- Membership in the lower edge is a plain signed-integer inequality. -/
lemma mem_bottom_edge (h m : ℕ) (k : Ch01.Band (2*h)) :
    k ∈ bottomEdge h m ↔ k.val ≤ -(h : ℤ)+(m : ℤ) := by
  simp [bottomEdge]

/-- Membership in the upper edge uses the complementary strict inequality. -/
lemma mem_top_edge (h m : ℕ) (k : Ch01.Band (2*h)) :
    k ∈ topEdge h m ↔ (h : ℤ)-(m : ℤ) < k.val := by
  simp [topEdge]

/-- Each lower edge contains exactly m modes when m does not exceed the half-band. -/
lemma bottom_edge_card (h m : ℕ) (hm : m ≤ h) :
    (bottomEdge h m).card = m := by
  classical
  have hin (k : Ch01.Band (2*h)) (hk : k ∈ bottomEdge h m) :
      (k.val+(h : ℤ)-1).toNat ∈ Finset.range m := by
    have hb := k.property
    have he := (mem_bottom_edge h m k).mp hk
    unfold Ch01.inBandPredicate at hb
    simp only [Finset.mem_range]
    push_cast at hb
    omega
  have hinj (k p : Ch01.Band (2*h)) (hk : k ∈ bottomEdge h m)
      (hp : p ∈ bottomEdge h m)
      (he : (k.val+(h : ℤ)-1).toNat = (p.val+(h : ℤ)-1).toNat) : k=p := by
    have hb := k.property
    have hc := p.property
    unfold Ch01.inBandPredicate at hb hc
    push_cast at hb hc
    apply Subtype.ext
    omega
  have hsurj (i : ℕ) (hi : i ∈ Finset.range m) :
      ∃ k, ∃ hk : k ∈ bottomEdge h m, (k.val+(h : ℤ)-1).toNat=i := by
    have hi' := Finset.mem_range.mp hi
    have hb : Ch01.inBandPredicate (2*h) (-(h : ℤ)+1+(i : ℤ)) := by
      unfold Ch01.inBandPredicate
      push_cast
      omega
    refine ⟨⟨-(h : ℤ)+1+(i : ℤ),hb⟩, ?_, ?_⟩
    · apply (mem_bottom_edge h m _).mpr
      dsimp
      omega
    · dsimp
      omega
  simpa using Finset.card_bij (fun k _ => (k.val+(h : ℤ)-1).toNat) hin
    (fun k hk p hp => hinj k p hk hp) hsurj

/-- The positive Nyquist convention still gives exactly m modes in the upper edge. -/
lemma top_edge_card (h m : ℕ) (hm : m ≤ h) :
    (topEdge h m).card = m := by
  classical
  have hin (k : Ch01.Band (2*h)) (hk : k ∈ topEdge h m) :
      ((h : ℤ)-k.val).toNat ∈ Finset.range m := by
    have hb := k.property
    have he := (mem_top_edge h m k).mp hk
    unfold Ch01.inBandPredicate at hb
    simp only [Finset.mem_range]
    push_cast at hb
    omega
  have hinj (k p : Ch01.Band (2*h)) (hk : k ∈ topEdge h m)
      (hp : p ∈ topEdge h m)
      (he : ((h : ℤ)-k.val).toNat = ((h : ℤ)-p.val).toNat) : k=p := by
    have hb := k.property
    have hc := p.property
    unfold Ch01.inBandPredicate at hb hc
    push_cast at hb hc
    apply Subtype.ext
    omega
  have hsurj (i : ℕ) (hi : i ∈ Finset.range m) :
      ∃ k, ∃ hk : k ∈ topEdge h m, ((h : ℤ)-k.val).toNat=i := by
    have hi' := Finset.mem_range.mp hi
    have hb : Ch01.inBandPredicate (2*h) ((h : ℤ)-(i : ℤ)) := by
      unfold Ch01.inBandPredicate
      push_cast
      omega
    refine ⟨⟨(h : ℤ)-(i : ℤ),hb⟩, ?_, ?_⟩
    · apply (mem_top_edge h m _).mpr
      dsimp
      omega
    · dsimp
      omega
  simpa using Finset.card_bij (fun k _ => ((h : ℤ)-k.val).toNat) hin
    (fun k hk p hp => hinj k p hk hp) hsurj

/-- The opposite shift matrix is exactly the diagonal difference of edge indicators.
No occupation or budget assumption appears in this finite matrix identity. -/
lemma opposite_edge_diagonal (h m : ℕ) (hm : m ≤ h) :
    edgeMatrix (2*h) (-(m : ℤ)) (m : ℤ) =
      Matrix.diagonal (fun k =>
        (if k ∈ bottomEdge h m then (1 : ℂ) else 0) -
        (if k ∈ topEdge h m then (1 : ℂ) else 0)) := by
  classical
  have _hm : m ≤ h := hm
  ext p k
  rw [opposite_shift_entry]
  by_cases he : p=k
  · subst p
    have hb := k.property
    unfold Ch01.inBandPredicate at hb
    have hplus : Ch01.inBandPredicate (2*h) (k.val+(m : ℤ)) ↔
        ¬ k ∈ topEdge h m := by
      rw [mem_top_edge]
      unfold Ch01.inBandPredicate
      push_cast at *
      omega
    have hminus : Ch01.inBandPredicate (2*h) (k.val-(m : ℤ)) ↔
        ¬ k ∈ bottomEdge h m := by
      rw [mem_bottom_edge]
      unfold Ch01.inBandPredicate
      push_cast at *
      omega
    simp only [ite_true, Matrix.diagonal_apply_eq, hplus, hminus]
    by_cases hl : k ∈ bottomEdge h m <;> by_cases ht : k ∈ topEdge h m <;> simp [hl,ht]
  · simp [he, Matrix.diagonal_apply_ne]

/-- Lift the actual diagonal matrix via dGamma; it is not a scalar on the full carrier. -/
lemma dGamma_opposite_edge (h m : ℕ) (hm : m ≤ h) :
    dGamma (edgeMatrix (2*h) (-(m : ℤ)) (m : ℤ)) = diagonalEdge h m := by
  classical
  rw [opposite_edge_diagonal h m hm]
  simp [dGamma, Matrix.diagonal_apply, diagonalEdge, bottomEdge, topEdge,
    Finset.sum_filter, sub_smul, Finset.sum_sub_distrib, Ch04.hopping_diagonal]

/-- Equality on all generating occupation kets extends linearly to the entire
fixed-charge coordinate budget. This is the shared span-induction bridge. -/
lemma action_on_budget (h : ℕ) (N K : ℤ) (A B : Ch09.Operators h)
    (hab : ∀ S : Ch07.Occupation h, Ch07.relativeCharge h S = N →
      Ch07.excitationEnergy h S ≤ K → A (A02.ket S) = B (A02.ket S)) :
    ∀ v ∈ Ch07.fixedBudget h N K, A v = B v := by
  intro v hv
  change v ∈ Submodule.span ℂ (A02.ket '' {S | Ch07.relativeCharge h S = N ∧ Ch07.excitationEnergy h S ≤ K}) at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    exact hab S hS.1 hS.2
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]

/-- A deeply occupied number operator acts as the identity on the whole coordinate
budget span, not merely on one configuration ket. Negative budgets contain zero only. -/
lemma number_frozen_full (h : ℕ) (hh : 0 < h) (N K : ℤ)
    (k : Ch01.Band (2*h)) (hk : k.val ≤ N-K) :
    ∀ v ∈ Ch07.fixedBudget h N K, Ch04.number k v = v := by
  have ht := action_on_budget h N K (Ch04.number k) 1 (by
    intro S hN he
    have hK : 0 ≤ K := le_trans (Ch07.excitation_nonneg h hh S) he
    have hc : (K.toNat : ℤ) = K := Int.toNat_of_nonneg hK
    have hok := Ch07.frozen_full h hh S N K.toNat hN (by simpa [hc] using he) k (by simpa [hc] using hk)
    have hn := Ch04.number_ket k S
    simp only [hok, ite_true, one_smul] at hn
    simpa [A02.ket, A02.occupationBasis, A02.occupationONB, Ch04.number, Ch04.creation, Ch04.annihilation, A02.extendBasis, Ch09.FockSpace, Ch07.FockSpace, Ch05.FockSpace] using hn)
  simpa using ht

/-- A high number operator vanishes on every budget vector; signed K permits word targets. -/
lemma number_frozen_empty (h : ℕ) (hh : 0 < h) (N K : ℤ)
    (k : Ch01.Band (2*h)) (hk : N+K < k.val) :
    ∀ v ∈ Ch07.fixedBudget h N K, Ch04.number k v = 0 := by
  have ht := action_on_budget h N K (Ch04.number k) 0 (by
    intro S hN he
    have hK : 0 ≤ K := le_trans (Ch07.excitation_nonneg h hh S) he
    have hc : (K.toNat : ℤ) = K := Int.toNat_of_nonneg hK
    have hok := Ch07.frozen_empty h hh S N K.toNat hN (by simpa [hc] using he) k (by simpa [hc] using hk)
    have hn := Ch04.number_ket k S
    simp only [hok, ite_false, zero_smul] at hn
    simpa [A02.ket, A02.occupationBasis, A02.occupationONB, Ch04.number, Ch04.creation, Ch04.annihilation, A02.extendBasis, Ch09.FockSpace, Ch07.FockSpace, Ch05.FockSpace] using hn)
  simpa using ht

/-- An empty source blocks a hop regardless of the target. -/
lemma hopping_empty_source (h : ℕ) (hh : 0 < h) (N K : ℤ)
    (p k : Ch01.Band (2*h)) (hk : N+K < k.val) :
    ∀ v ∈ Ch07.fixedBudget h N K, Ch04.hopping p k v = 0 := by
  have ht := action_on_budget h N K (Ch04.hopping p k) 0 (by
    intro S hN he
    have hK : 0 ≤ K := le_trans (Ch07.excitation_nonneg h hh S) he
    have hc : (K.toNat : ℤ) = K := Int.toNat_of_nonneg hK
    apply Ch04.hopping_blocked
    exact Or.inl (Ch07.frozen_empty h hh S N K.toNat hN (by simpa [hc] using he) k (by simpa [hc] using hk)))
  simpa using ht

/-- A full target blocks an off-diagonal hop. The p≠k condition excludes number action. -/
lemma hopping_full_target (h : ℕ) (hh : 0 < h) (N K : ℤ)
    (p k : Ch01.Band (2*h)) (hpk : p ≠ k) (hp : p.val ≤ N-K) :
    ∀ v ∈ Ch07.fixedBudget h N K, Ch04.hopping p k v = 0 := by
  have ht := action_on_budget h N K (Ch04.hopping p k) 0 (by
    intro S hN he
    have hK : 0 ≤ K := le_trans (Ch07.excitation_nonneg h hh S) he
    have hc : (K.toNat : ℤ) = K := Int.toNat_of_nonneg hK
    apply Ch04.hopping_blocked
    exact Or.inr ⟨hpk, Ch07.frozen_full h hh S N K.toNat hN (by simpa [hc] using he) p (by simpa [hc] using hp)⟩)
  simpa using ht

/-- The M1 buffer places every lower edge inside the occupied frozen margin. -/
lemma bottom_edge_full (h m K : ℕ) (hh : 0 < h) (N : ℤ)
    (hm : (m : ℤ)+(K : ℤ)+|N| ≤ (h : ℤ))
    (k : Ch01.Band (2*h)) (hk : k ∈ bottomEdge h m) :
    ∀ v ∈ Ch07.fixedBudget h N (K : ℤ), Ch04.number k v = v := by
  intro v hv
  apply number_frozen_full h hh N (K : ℤ) k _ v hv
  have hk' := (mem_bottom_edge h m k).mp hk
  have hN := neg_abs_le N
  omega

/-- The same M1 buffer places every upper edge inside the empty frozen margin. -/
lemma top_edge_empty (h m K : ℕ) (hh : 0 < h) (N : ℤ)
    (hm : (m : ℤ)+(K : ℤ)+|N| ≤ (h : ℤ))
    (k : Ch01.Band (2*h)) (hk : k ∈ topEdge h m) :
    ∀ v ∈ Ch07.fixedBudget h N (K : ℤ), Ch04.number k v = 0 := by
  intro v hv
  apply number_frozen_empty h hh N (K : ℤ) k _ v hv
  have hk' := (mem_top_edge h m k).mp hk
  have hN := le_abs_self N
  omega

/-- Exact edge occupation evaluates to m on a natural-energy budget under M1. -/
lemma diagonal_edge_budget (h m K : ℕ) (hh : 0 < h) (N : ℤ)
    (hm : (m : ℤ)+(K : ℤ)+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N (K : ℤ), diagonalEdge h m v = (m : ℂ) • v := by
  classical
  intro v hv
  have hmh : m ≤ h := by
    have hN := abs_nonneg N
    omega
  simp only [diagonalEdge, LinearMap.sub_apply, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl (fun k hk => bottom_edge_full h m K hh N hm k hk v hv),
    Finset.sum_congr rfl (fun k hk => top_edge_empty h m K hh N hm k hk v hv)]
  simp only [Finset.sum_const, bottom_edge_card h m hmh, nsmul_zero, sub_zero]
  exact (Nat.cast_smul_eq_nsmul ℂ m v).symm

/-- Under M2 each nonzero unequal mixed edge coefficient has both endpoints in
one frozen boundary region. Bottom targets and top sources give Pauli blocking. -/
lemma mixed_edge_hopping_zero (h : ℕ) (hh : 0 < h) (m n N K : ℤ)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hmn : m ≠ n)
    (hmargin : m+n+K+|N| ≤ (h : ℤ)) (p k : Ch01.Band (2*h))
    (he : edgeMatrix (2*h) (-m) n p k ≠ 0) :
    ∀ v ∈ Ch07.fixedBudget h N K, Ch04.hopping p k v = 0 := by
  obtain ⟨hpk, hbot | htop⟩ := mixed_edge_support_even h m n hm hn p k he
  · apply hopping_full_target h hh N K p k
    · intro heq
      have hval := congrArg Subtype.val heq
      omega
    · have ha := neg_abs_le N
      omega
  · apply hopping_empty_source h hh N K p k
    have ha := le_abs_self N
    omega

/-- Summing blocked actual edge hoppings annihilates every budget vector. -/
lemma mixed_edge_budget_zero (h : ℕ) (hh : 0 < h) (m n N K : ℤ)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hmn : m ≠ n)
    (hmargin : m+n+K+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N K, dGamma (edgeMatrix (2*h) (-m) n) v = 0 := by
  intro v hv
  simp only [dGamma, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro p _
  apply Finset.sum_eq_zero
  intro k _
  by_cases he : edgeMatrix (2*h) (-m) n p k = 0
  · simp only [he, zero_smul]
  · rw [mixed_edge_hopping_zero h hh m n N K hm hn hmn hmargin p k he v hv, smul_zero]
end Bosonize.A04
