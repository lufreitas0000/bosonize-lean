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
      A04.diagonalEdge h m := by
  rw [Ch09.rho_commutator_edge, A04.dGamma_opposite_edge h m hm]

/-- The useful same-mode M1 bound is m+K+|N|≤h; no artificial 2m is required. -/
lemma rho_schwinger_m1 (h m K : ℕ) (hh : 0 < h) (N : ℤ)
    (hmargin : (m : ℤ)+(K : ℤ)+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N (K : ℤ),
      A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (m : ℤ)) v =
        (m : ℂ) • v := by
  have hm : m ≤ h := by have hn := abs_nonneg N; omega
  rw [rho_opposite_edge h m hm]
  exact A04.diagonal_edge_budget h m K hh N hmargin

/-- Same-mode scalar action also accepts signed budgets; a negative budget is zero. -/
lemma rho_schwinger_signed (h : ℕ) (hh : 0 < h) (m : ℕ) (N K : ℤ)
    (hmargin : (m : ℤ)+K+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (m : ℤ)) v =
        (m : ℂ) • v := by
  by_cases hk : K < 0
  · intro v hv
    rw [Ch07.negative_budget h hh N K hk] at hv
    have hv0 : v = 0 := hv
    simp [hv0]
  · have hK : (K.toNat : ℤ) = K := by omega
    have hb := rho_schwinger_m1 h m K.toNat hh N (by simpa [hK] using hmargin)
    simpa [hK] using hb

/-- Unequal signed modes have zero commutator action under the genuine two-mode margin. -/
lemma rho_offdiagonal_m2 (h : ℕ) (hh : 0 < h) (m n N K : ℤ)
    (hmn : m+n ≠ 0) (hmargin : |m|+|n|+K+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      A02.commutator (Ch09.rho h m) (Ch09.rho h n) v = 0 := by
  by_cases hm : 0 ≤ m
  · by_cases hn : 0 ≤ n
    · rw [Ch09.rho_positive_commute h m n hm hn]
      simp
    · have hswap : A02.commutator (Ch09.rho h m) (Ch09.rho h n) =
          -A02.commutator (Ch09.rho h n) (Ch09.rho h m) := by unfold A02.commutator; abel
      rw [hswap, Ch09.rho_commutator_edge]
      have hz := A04.mixed_edge_budget_zero h hh (-n) m N K (by omega) hm
        (by omega) (by rw [abs_of_nonneg hm, abs_of_neg (by omega : n < 0)] at hmargin; omega)
      simpa using fun v hv => congrArg Neg.neg (hz v hv)
  · by_cases hn : 0 ≤ n
    · rw [Ch09.rho_commutator_edge]
      have hz := A04.mixed_edge_budget_zero h hh (-m) n N K (by omega) hn
        (by omega) (by simpa [abs_of_neg (by omega : m < 0), abs_of_nonneg hn] using hmargin)
      simpa using hz
    · rw [Ch09.rho_negative_commute h m n (by omega) (by omega)]
      simp

/-- Combining opposite and unequal modes preserves the sign for arbitrary integer labels. -/
lemma rho_signed_ccr (h : ℕ) (hh : 0 < h) (m n N K : ℤ)
    (hmargin : |m|+|n|+K+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      A02.commutator (Ch09.rho h m) (Ch09.rho h n) v =
        schwingerCoefficient m n • v := by
  by_cases hmn : m+n=0
  · have hn : n = -m := by omega
    subst n
    by_cases hm : m ≤ 0
    · have hc : ((-m).toNat : ℤ) = -m := by omega
      have hb := rho_schwinger_signed h hh (-m).toNat N K (by
        have hp := abs_nonneg m
        rw [abs_neg] at hmargin
        rw [hc]
        rw [abs_of_nonpos hm] at hmargin
        omega)
      intro v hv
      have he := hb v hv
      have hcC : ((-m).toNat : ℂ) = -(m : ℂ) := by exact_mod_cast hc
      simpa [hc, hcC, schwingerCoefficient] using he
    · have hc : (m.toNat : ℤ) = m := by omega
      have hb := rho_schwinger_signed h hh m.toNat N K (by
        rw [hc]
        rw [abs_neg, abs_of_pos (by omega : 0 < m)] at hmargin
        omega)
      have hswap : A02.commutator (Ch09.rho h m) (Ch09.rho h (-m)) =
          -A02.commutator (Ch09.rho h (-m)) (Ch09.rho h m) := by unfold A02.commutator; abel
      intro v hv
      rw [hswap, LinearMap.neg_apply]
      have he := hb v hv
      rw [hc] at he
      have hcC : (m.toNat : ℂ) = (m : ℂ) := by exact_mod_cast hc
      rw [he, hcC]
      simp [schwingerCoefficient]
  · simpa [schwingerCoefficient, hmn] using rho_offdiagonal_m2 h hh m n N K hmn hmargin

/-- Subtracting the scalar sea term at transfer zero leaves every commutator unchanged. -/
lemma normal_commutator_eq (h : ℕ) (m n : ℤ) :
    A02.commutator (Ch09.normalRho h m) (Ch09.normalRho h n) =
      A02.commutator (Ch09.rho h m) (Ch09.rho h n) := by
  by_cases hm : m=0 <;> by_cases hn : n=0 <;>
    simp only [Ch09.normalRho, hm, hn, ite_true, ite_false, sub_zero, A02.commutator,
      sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] <;> abel

/-- Normal ordering respects the same local two-mode restricted identity. -/
lemma normal_signed_ccr (h : ℕ) (hh : 0 < h) (m n N K : ℤ)
    (hmargin : |m|+|n|+K+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      A02.commutator (Ch09.normalRho h m) (Ch09.normalRho h n) v =
        schwingerCoefficient m n • v := by
  rw [normal_commutator_eq]
  exact rho_signed_ccr h hh m n N K hmargin

/-- A single uniform cutoff implies every local pair bound, while retaining input action. -/
lemma normal_uniform_ccr (h M : ℕ) (hh : 0 < h) (m n N K : ℤ)
    (hm : |m| ≤ (M : ℤ)) (hn : |n| ≤ (M : ℤ))
    (hmargin : 2*(M : ℤ)+K+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      A02.commutator (Ch09.normalRho h m) (Ch09.normalRho h n) v =
        schwingerCoefficient m n • v := by
  exact normal_signed_ccr h hh m n N K (by omega)

/-- The twisted inverse-Fourier dictionary identifies every chosen boundary twist
with the same integer-truncated partial current. Cyclic site coefficients are excluded. -/
lemma reconstructed_density_ccr (h : ℕ) [NeZero (2*h)] (hh : 0 < h)
    (b : Ch06Ext.BoundaryTwist (2*h)) (m n N K : ℤ)
    (hmargin : |m|+|n|+K+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      A02.commutator (Ch09.reconstructedDensity (2*h) b m)
        (Ch09.reconstructedDensity (2*h) b n) v =
        schwingerCoefficient m n • v := by
  simp only [Ch09.reconstructed_density]
  exact rho_signed_ccr h hh m n N K hmargin

/-- The empty application word is the ambient identity, so excursion tracking starts
at the original input rather than at an invented shifted budget. -/
lemma density_word_nil (h : ℕ) : densityWord h [] = 1 := by
  simp [densityWord, A03.applicationWord]

/-- List order is application order: after the first current acts, the tail acts. -/
lemma density_word_cons (h : ℕ) (d : ℤ) (ds : List ℤ) :
    densityWord h (d::ds) = densityWord h ds * Ch09.rho h d := by
  simp [densityWord, A03.applicationWord, List.prod_append]

/-- Every density word preserves charge and has the exact signed total energy shift
at the filtered-budget level. No CCR hypothesis is required for this map. -/
lemma density_word_filtered (h : ℕ) (ds : List ℤ) :
    A03.Filtered (Ch07.relativeCharge h) (Ch07.excitationEnergy h)
      (densityWord h ds) 0 ds.sum := by
  induction ds with
  | nil => simpa only [density_word_nil, List.sum_nil] using A03.filtered_identity (Ch07.relativeCharge h) (Ch07.excitationEnergy h)
  | cons d ds ih =>
    rw [density_word_cons, List.sum_cons]
    simpa only [zero_add] using A03.filtered_comp (Ch07.relativeCharge h) (Ch07.excitationEnergy h)
      (densityWord h ds) (Ch09.rho h d) 0 ds.sum 0 d ih
      (A03.exact_shift_filtered _ _ _ 0 d (Ch09.rho_exact_shift h d))

/-- The output budget uses the actual sum of signed transfers, not the sum of positives. -/
lemma density_word_budget (h : ℕ) (ds : List ℤ) (N K : ℤ) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      densityWord h ds v ∈ Ch07.fixedBudget h N (K+ds.sum) := by
  simpa only [add_zero, Ch07.fixedBudget] using A03.filtered_budget_map (Ch07.relativeCharge h) (Ch07.excitationEnergy h)
    (densityWord h ds) 0 ds.sum N K (density_word_filtered h ds)

/-- Every prefix has its own exact signed target budget before enlargement to
one uniform excursion bound. Prefixes here are the applied right suffixes. -/
lemma density_word_prefix_exact_budget (h : ℕ) (ds : List ℤ) (r : ℕ) (N K : ℤ) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      densityWord h (ds.take r) v ∈ Ch07.fixedBudget h N (K+(ds.take r).sum) := by
  exact density_word_budget h (ds.take r) N K

/-- Each application prefix fits the maximum upward excursion of the whole list. -/
lemma density_word_prefix_budget (h : ℕ) (ds : List ℤ) (r : ℕ) (N K : ℤ) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      densityWord h (ds.take r) v ∈
        Ch07.fixedBudget h N (K+A03.upwardExcursion ds) := by
  let word : List (A03.Operators (Ch01.Band (2*h)) × ℤ) := ds.map (fun d => (Ch09.rho h d, d))
  have hw : ∀ step ∈ word, A03.Filtered (Ch07.relativeCharge h) (Ch07.excitationEnergy h) step.1 0 step.2 := by
    intro step hs
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hs
    exact A03.exact_shift_filtered _ _ _ 0 d (Ch09.rho_exact_shift h d)
  have hp := A03.charge_preserving_word_prefix (Ch07.relativeCharge h) (Ch07.excitationEnergy h) word hw N K r
  simpa [word, List.map_map, Function.comp_def, ← List.map_take, densityWord, Ch07.fixedBudget] using hp

/-- Insert a CCR at the state produced by the right suffix (application prefix).
The margin is on that input only; it does not demand both commutator factors preserve it. -/
lemma normal_ccr_after_prefix (h M : ℕ) (hh : 0 < h) (ds : List ℤ) (r : ℕ)
    (m n N K : ℤ) (hm : |m| ≤ (M : ℤ)) (hn : |n| ≤ (M : ℤ))
    (hmargin : 2*(M : ℤ)+K+A03.upwardExcursion ds+|N| ≤ (h : ℤ)) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      A02.commutator (Ch09.normalRho h m) (Ch09.normalRho h n)
        (densityWord h (ds.take r) v) =
      schwingerCoefficient m n • densityWord h (ds.take r) v := by
  intro v hv
  exact normal_uniform_ccr h M hh m n N (K+A03.upwardExcursion ds) hm hn
    (by omega) _ (density_word_prefix_budget h ds r N K v hv)

/-- A written product equals the application word of its reversed labels. -/
lemma written_word_eq (h : ℕ) (ds : List ℤ) :
    (ds.map (Ch09.rho h)).prod = densityWord h ds.reverse := by
  simp [densityWord, A03.applicationWord, List.map_reverse]

/-- Written right suffixes carry the prefix budget of the reversed application list. -/
lemma written_suffix_budget (h : ℕ) (ds : List ℤ) (r : ℕ) (N K : ℤ) :
    ∀ v ∈ Ch07.fixedBudget h N K,
      densityWord h (ds.reverse.take r) v ∈
        Ch07.fixedBudget h N (K+writtenExcursion ds) := by
  exact density_word_prefix_budget h ds.reverse r N K

/-- Nonzero sector grounds witness that the fixed budgets under discussion are
inhabited; admissibility and nonnegative K are explicit. -/
lemma ground_budget_witness (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ) :
    ∃ v ∈ Ch07.fixedBudget h N (K : ℤ), v ≠ 0 := by
  exact ⟨Ch07.groundKet h N hN, Ch07.ground_ket_mem_budget h hh N hN K,
    Ch07.ground_ket_ne_zero h N hN⟩

/-- The exact edge commutator annihilates the empty occupation vector, exhibiting
why no nonzero scalar current CCR can hold on the whole finite Fock carrier. -/
lemma rho_empty_commutator (h m : ℕ) :
    A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (m : ℤ))
      (A02.ket (∅ : Ch07.Occupation h)) = 0 := by
  have hz (d : ℤ) : Ch09.rho h d (A02.ket (∅ : Ch07.Occupation h)) = 0 := by
    rw [Ch09.rho, A04.dGamma]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro k hk
    have hb := Ch04.hopping_blocked p k (∅ : Ch07.Occupation h) (Or.inl (by simp))
    convert congrArg (fun v => A04.shift (2*h) d p k • v) hb using 1 <;>
      simp [A02.ket, A02.occupationBasis, A02.occupationONB, Ch04.hopping,
        Ch04.creation, Ch04.annihilation, A02.extendBasis, Ch09.FockSpace,
        Ch07.FockSpace, Ch05.FockSpace]
  simp [A02.commutator, LinearMap.sub_apply, Module.End.mul_apply, hz]

/-- This concrete empty-ket test forbids the unrestricted scalar operator equality. -/
lemma rho_global_scalar_impossible (h m : ℕ) (hm : 0 < m) :
    A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (m : ℤ)) ≠
      (m : ℂ) • (1 : Ch09.Operators h) := by
  intro he
  have hb := congrArg (fun A : Ch09.Operators h => A (A02.ket (∅ : Ch07.Occupation h))) he
  rw [rho_empty_commutator] at hb
  have hc : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hk := A02.ket_ne_zero (∅ : Ch07.Occupation h)
  have hn : (m : ℂ) • A02.ket (∅ : Ch07.Occupation h) ≠ 0 := smul_ne_zero hc hk
  apply hn
  simpa using hb.symm
end Bosonize.Ch10
