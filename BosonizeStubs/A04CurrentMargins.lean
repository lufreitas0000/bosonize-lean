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
    k ∈ bottomEdge h m ↔ k.val ≤ -(h : ℤ)+(m : ℤ) := by sorry

/-- Membership in the upper edge uses the complementary strict inequality. -/
lemma mem_top_edge (h m : ℕ) (k : Ch01.Band (2*h)) :
    k ∈ topEdge h m ↔ (h : ℤ)-(m : ℤ) < k.val := by sorry

/-- Each lower edge contains exactly m modes when m does not exceed the half-band. -/
lemma bottom_edge_card (h m : ℕ) (hm : m ≤ h) :
    (bottomEdge h m).card = m := by sorry

/-- The positive Nyquist convention still gives exactly m modes in the upper edge. -/
lemma top_edge_card (h m : ℕ) (hm : m ≤ h) :
    (topEdge h m).card = m := by sorry

/-- The opposite shift matrix is exactly the diagonal difference of edge indicators.
No occupation or budget assumption appears in this finite matrix identity. -/
lemma opposite_edge_diagonal (h m : ℕ) (hm : m ≤ h) :
    edgeMatrix (2*h) (-(m : ℤ)) (m : ℤ) =
      Matrix.diagonal (fun k =>
        (if k ∈ bottomEdge h m then (1 : ℂ) else 0) -
        (if k ∈ topEdge h m then (1 : ℂ) else 0)) := by sorry

/-- Lift the actual diagonal matrix via dGamma; it is not a scalar on the full carrier. -/
lemma dGamma_opposite_edge (h m : ℕ) (hm : m ≤ h) :
    dGamma (edgeMatrix (2*h) (-(m : ℤ)) (m : ℤ)) = diagonalEdge h m := by sorry

/-- Equality on all generating occupation kets extends linearly to the entire
fixed-charge coordinate budget. This is the shared span-induction bridge. -/
lemma action_on_budget (h : ℕ) (N K : ℤ) (A B : Ch09.Operators h)
    (hab : ∀ S : Ch07.Occupation h, Ch07.relativeCharge h S = N →
      Ch07.excitationEnergy h S ≤ K → A (A02.ket S) = B (A02.ket S)) :
    ∀ v ∈ Ch07.fixedBudget h N K, A v = B v := by sorry

/-- A deeply occupied number operator acts as the identity on the whole coordinate
budget span, not merely on one configuration ket. Negative budgets contain zero only. -/
lemma number_frozen_full (h : ℕ) (hh : 0 < h) (N K : ℤ)
    (k : Ch01.Band (2*h)) (hk : k.val ≤ N-K) :
    ∀ v ∈ Ch07.fixedBudget h N K, Ch04.number k v = v := by sorry

/-- A high number operator vanishes on every budget vector; signed K permits word targets. -/
lemma number_frozen_empty (h : ℕ) (hh : 0 < h) (N K : ℤ)
    (k : Ch01.Band (2*h)) (hk : N+K < k.val) :
    ∀ v ∈ Ch07.fixedBudget h N K, Ch04.number k v = 0 := by sorry

/-- An empty source blocks a hop regardless of the target. -/
lemma hopping_empty_source (h : ℕ) (hh : 0 < h) (N K : ℤ)
    (p k : Ch01.Band (2*h)) (hk : N+K < k.val) :
    ∀ v ∈ Ch07.fixedBudget h N K, Ch04.hopping p k v = 0 := by sorry

/-- A full target blocks an off-diagonal hop. The p≠k condition excludes number action. -/
lemma hopping_full_target (h : ℕ) (hh : 0 < h) (N K : ℤ)
    (p k : Ch01.Band (2*h)) (hpk : p ≠ k) (hp : p.val ≤ N-K) :
    ∀ v ∈ Ch07.fixedBudget h N K, Ch04.hopping p k v = 0 := by sorry

/-- The M1 buffer places every lower edge inside the occupied frozen margin. -/
lemma bottom_edge_full (h m K : ℕ) (hh : 0 < h) (N : ℤ)
    (hm : (m : ℤ)+(K : ℤ)+|N| ≤ (h : ℤ))
    (k : Ch01.Band (2*h)) (hk : k ∈ bottomEdge h m) :
    ∀ v ∈ Ch07.fixedBudget h N (K : ℤ), Ch04.number k v = v := by sorry

/-- The same M1 buffer places every upper edge inside the empty frozen margin. -/
lemma top_edge_empty (h m K : ℕ) (hh : 0 < h) (N : ℤ)
    (hm : (m : ℤ)+(K : ℤ)+|N| ≤ (h : ℤ))
    (k : Ch01.Band (2*h)) (hk : k ∈ topEdge h m) :
    ∀ v ∈ Ch07.fixedBudget h N (K : ℤ), Ch04.number k v = 0 := by sorry

/-- Exact edge occupation evaluates to m on a natural-energy budget under M1. -/
lemma diagonal_edge_budget (h m K : ℕ) (hh : 0 < h) (N : ℤ)
    (hm : (m : ℤ)+(K : ℤ)+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N (K : ℤ), diagonalEdge h m v = (m : ℂ) • v := by sorry

/-- Under M2 each nonzero unequal mixed edge coefficient has both endpoints in
one frozen boundary region. Bottom targets and top sources give Pauli blocking. -/
lemma mixed_edge_hopping_zero (h : ℕ) (hh : 0 < h) (m n N K : ℤ)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hmn : m ≠ n)
    (hmargin : m+n+K+|N| ≤ (h : ℤ)) (p k : Ch01.Band (2*h))
    (he : edgeMatrix (2*h) (-m) n p k ≠ 0) :
    ∀ v ∈ Ch07.fixedBudget h N K, Ch04.hopping p k v = 0 := by sorry

/-- Summing blocked actual edge hoppings annihilates every budget vector. -/
lemma mixed_edge_budget_zero (h : ℕ) (hh : 0 < h) (m n N K : ℤ)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hmn : m ≠ n)
    (hmargin : m+n+K+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N K, dGamma (edgeMatrix (2*h) (-m) n) v = 0 := by sorry
end Bosonize.A04
