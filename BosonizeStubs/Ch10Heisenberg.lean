module
public import BosonizeStubs.A04CurrentMargins
/-! # CH10 finite restricted Heisenberg algebra
Phase A. All identities concern the concrete fermionic currents on specified inputs.
Written products act rightmost first; application lists act in list order.
-/
@[expose] public section
namespace Bosonize.Ch10
open scoped BigOperators Classical

/-- Density words in application order: the first listed transfer acts first. -/
noncomputable def densityWord (h : ℕ) (ds : List ℤ) : Ch09.Operators h :=
  A03.applicationWord (ds.map (Ch09.rho h))

/-- For a written left-to-right product, reverse its mode list before tracking input
excursions. This prevents left prefixes from being mistaken for right suffixes. -/
def writtenExcursion (ds : List ℤ) : ℤ := A03.upwardExcursion ds.reverse

/-- The signed Schwinger coefficient for the convention [rho_m,rho_n]=-m δ_(m+n,0). -/
def schwingerCoefficient (m n : ℤ) : ℂ := if m+n=0 then -(m : ℂ) else 0

/-- The exact full-space diagonal commutator retains bottom-minus-top occupation. -/
lemma rho_opposite_edge (h m : ℕ) (hm : m ≤ h) :
    A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (m : ℤ)) =
      A04.diagonalEdge h m := by sorry

/-- The useful same-mode M1 bound is m+K+|N|≤h; no artificial 2m is required. -/
lemma rho_schwinger_m1 (h m K : ℕ) (hh : 0 < h) (N : ℤ)
    (hmargin : (m : ℤ)+(K : ℤ)+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N (K : ℤ),
      A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (m : ℤ)) v =
        (m : ℂ) • v := by sorry

/-- Same-mode scalar action also accepts signed budgets; a negative budget is zero. -/
lemma rho_schwinger_signed (h : ℕ) (hh : 0 < h) (m : ℕ) (N K : ℤ)
    (hmargin : (m : ℤ)+K+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (m : ℤ)) v =
        (m : ℂ) • v := by sorry

/-- Unequal signed modes have zero commutator action under the genuine two-mode margin. -/
lemma rho_offdiagonal_m2 (h : ℕ) (hh : 0 < h) (m n N K : ℤ)
    (hmn : m+n ≠ 0) (hmargin : |m|+|n|+K+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      A02.commutator (Ch09.rho h m) (Ch09.rho h n) v = 0 := by sorry

/-- Combining opposite and unequal modes preserves the sign for arbitrary integer labels. -/
lemma rho_signed_ccr (h : ℕ) (hh : 0 < h) (m n N K : ℤ)
    (hmargin : |m|+|n|+K+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      A02.commutator (Ch09.rho h m) (Ch09.rho h n) v =
        schwingerCoefficient m n • v := by sorry

/-- Subtracting the scalar sea term at transfer zero leaves every commutator unchanged. -/
lemma normal_commutator_eq (h : ℕ) (m n : ℤ) :
    A02.commutator (Ch09.normalRho h m) (Ch09.normalRho h n) =
      A02.commutator (Ch09.rho h m) (Ch09.rho h n) := by sorry

/-- Normal ordering respects the same local two-mode restricted identity. -/
lemma normal_signed_ccr (h : ℕ) (hh : 0 < h) (m n N K : ℤ)
    (hmargin : |m|+|n|+K+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      A02.commutator (Ch09.normalRho h m) (Ch09.normalRho h n) v =
        schwingerCoefficient m n • v := by sorry

/-- A single uniform cutoff implies every local pair bound, while retaining input action. -/
lemma normal_uniform_ccr (h M : ℕ) (hh : 0 < h) (m n N K : ℤ)
    (hm : |m| ≤ (M : ℤ)) (hn : |n| ≤ (M : ℤ))
    (hmargin : 2*(M : ℤ)+K+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      A02.commutator (Ch09.normalRho h m) (Ch09.normalRho h n) v =
        schwingerCoefficient m n • v := by sorry

/-- The twisted inverse-Fourier dictionary identifies every chosen boundary twist
with the same integer-truncated partial current. Cyclic site coefficients are excluded. -/
lemma reconstructed_density_ccr (h : ℕ) [NeZero (2*h)] (hh : 0 < h)
    (b : Ch06Ext.BoundaryTwist (2*h)) (m n N K : ℤ)
    (hmargin : |m|+|n|+K+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      A02.commutator (Ch09.reconstructedDensity (2*h) b m)
        (Ch09.reconstructedDensity (2*h) b n) v =
        schwingerCoefficient m n • v := by sorry

/-- The empty application word is the ambient identity, so excursion tracking starts
at the original input rather than at an invented shifted budget. -/
lemma density_word_nil (h : ℕ) : densityWord h [] = 1 := by sorry

/-- List order is application order: after the first current acts, the tail acts. -/
lemma density_word_cons (h : ℕ) (d : ℤ) (ds : List ℤ) :
    densityWord h (d::ds) = densityWord h ds * Ch09.rho h d := by sorry

/-- Every density word preserves charge and has the exact signed total energy shift
at the filtered-budget level. No CCR hypothesis is required for this map. -/
lemma density_word_filtered (h : ℕ) (ds : List ℤ) :
    A03.Filtered (Ch07.relativeCharge h) (Ch07.excitationEnergy h)
      (densityWord h ds) 0 ds.sum := by sorry

/-- The output budget uses the actual sum of signed transfers, not the sum of positives. -/
lemma density_word_budget (h : ℕ) (ds : List ℤ) (N K : ℤ) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      densityWord h ds v ∈ Ch07.fixedBudget h N (K+ds.sum) := by sorry

/-- Every prefix has its own exact signed target budget before enlargement to
one uniform excursion bound. Prefixes here are the applied right suffixes. -/
lemma density_word_prefix_exact_budget (h : ℕ) (ds : List ℤ) (r : ℕ) (N K : ℤ) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      densityWord h (ds.take r) v ∈ Ch07.fixedBudget h N (K+(ds.take r).sum) := by sorry

/-- Each application prefix fits the maximum upward excursion of the whole list. -/
lemma density_word_prefix_budget (h : ℕ) (ds : List ℤ) (r : ℕ) (N K : ℤ) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      densityWord h (ds.take r) v ∈
        Ch07.fixedBudget h N (K+A03.upwardExcursion ds) := by sorry

/-- Insert a CCR at the state produced by the right suffix (application prefix).
The margin is on that input only; it does not demand both commutator factors preserve it. -/
lemma normal_ccr_after_prefix (h M : ℕ) (hh : 0 < h) (ds : List ℤ) (r : ℕ)
    (m n N K : ℤ) (hm : |m| ≤ (M : ℤ)) (hn : |n| ≤ (M : ℤ))
    (hmargin : 2*(M : ℤ)+K+A03.upwardExcursion ds+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      A02.commutator (Ch09.normalRho h m) (Ch09.normalRho h n)
        (densityWord h (ds.take r) v) =
      schwingerCoefficient m n • densityWord h (ds.take r) v := by sorry

/-- A written product equals the application word of its reversed labels. -/
lemma written_word_eq (h : ℕ) (ds : List ℤ) :
    (ds.map (Ch09.rho h)).prod = densityWord h ds.reverse := by sorry

/-- Written right suffixes carry the prefix budget of the reversed application list. -/
lemma written_suffix_budget (h : ℕ) (ds : List ℤ) (r : ℕ) (N K : ℤ) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      densityWord h (ds.reverse.take r) v ∈
        Ch07.fixedBudget h N (K+writtenExcursion ds) := by sorry

/-- Nonzero sector grounds witness that the fixed budgets under discussion are
inhabited; admissibility and nonnegative K are explicit. -/
lemma ground_budget_witness (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) :
    ∃ v ∈ Ch07.fixedBudget h N (K : ℤ), v ≠ 0 := by sorry

/-- The exact edge commutator annihilates the empty occupation vector, exhibiting
why no nonzero scalar current CCR can hold on the whole finite Fock carrier. -/
lemma rho_empty_commutator (h m : ℕ) :
    A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (m : ℤ))
      (A02.ket (∅ : Ch07.Occupation h)) = 0 := by sorry

/-- This concrete empty-ket test forbids the unrestricted scalar operator equality. -/
lemma rho_global_scalar_impossible (h m : ℕ) (hm : 0 < m) :
    A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (m : ℤ)) ≠
      (m : ℂ) • (1 : Ch09.Operators h) := by sorry
end Bosonize.Ch10
