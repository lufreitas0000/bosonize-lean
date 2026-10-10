# Ch10Heisenberg: formal companion

Phase A draft, 2026-10-10. Independent Phase A review passed; the reviewed interface is now locked.
Phase B proofs are pending. **21 theorem stubs, each exactly one `by sorry`**, three fully elaborated
data constructions. Source SHA-256: `3da47f8454feb3921b446433ced39712f1e5b010635f298d3f9f779fd55ed2dc`. The exact snapshot below records all
signatures and definitions. A successful build establishes elaboration, not proofs.

## Sources and reconciliation

Read [Chapter 10](../../../notes/md/ch10_Heisenberg_algebra.md),
[A04 reference and constructive lecture](../../../notes/appendices/a04_density_partitions_and_sugawara.md),
[A03 budget lecture](../../../notes/appendices/a03_energy_budgets_and_filtered_maps.md)
and existing Core A04DensityKinematics, CH07VacuumBudget, CH09DensityModes,
A03EnergyBudgets. Chapter 10 §§10.1–10.5 supplies exact finite edges, M1/M2
restricted action, signed normal current CCR and word input-margin accounting.
The partition bijection, Gram theorem, completeness and Sugawara portion of A04
is explicitly deferred. Existing Core bytes and locks remain untouched.

There are no active `docs/stub_suggestion/` or `docs/proof_suggestion/` directories
at this checkpoint. The historical `note/proof_suggestions_revision_2026-10-09.md`
is advisory snapshot material, not a proof or a currently active suggested source.
The formalizer skill requests Flash/Pro model tiers, but neither provider is exposed
to this session. The authorized draft uses the inherited available model fallback;
no unavailable provider is represented as having run.

## Mathematical contract and proof dependencies

All operators act on the actual finite fermionic occupation Hilbert space.
The signed band is the positive-Nyquist interval `Ch01.Band (2*h)`; partial shifts
use equality of integer labels and never cyclic residue addition. Second quantization
is the existing concrete CAR Lie map. No oscillator CCR is assumed.

The lower edge is -h+1 through -h+m; the upper edge is h-m+1 through h.
Opposite shifts give **bottom minus top**. M1 is m+K+|N|≤h with natural K;
it is deliberately weaker than the uniform two-mode bound. The admissible example
h=2,m=1,K=1,N=0 fits M1 while a uniform 2m bound does not.
Signed-budget action supports intermediate word targets. If K<0, first use
`Ch07.negative_budget`, because m≤h need not follow from a signed margin in
that empty-budget case. Only after K≥0 may signed-to-natural casting use
K.toNat and apply cardinality/diagonal edge identities.

The span bridge `A04.action_on_budget` extends ket action linearly. Lower frozen
occupation uses `Ch07.frozen_full` and `Ch04.number_ket`; upper emptiness uses
`Ch07.frozen_empty`. Off-diagonal bottom hops require a full destination and
p≠k; the latter follows from m≠n and the actual transfer p=k+n-m. Upper hops
have an empty source. `A04.mixed_edge_support_even` gives **both endpoints**;
a source-only bottom assertion would be insufficient. Summing zero coefficient
terms and these blocked nonzero terms gives the M2 edge action.

CH10 combines same-sign global commutation with the concrete mixed edge action.
Normal ordering subtracts a central scalar at transfer zero, so it preserves
commutators. The signed coefficient is -m when m+n=0 and zero otherwise.
Input-vector identities remain restricted action identities, never global scalar
endomorphism equalities or false CCR on a finite compressed carrier.

Words use A03's `applicationWord = reverse.prod`. The first listed mode acts first.
For a written left-to-right product, reverse the mode list. Each take-prefix has
its exact target K+sum; the maximum cumulative signed upward excursion enlarges
all prefix targets to a common budget. Existing CH09 exact shift and A03 filtered
word/prefix APIs prove these maps independently of CCR. The commutator is applied
only to the resulting suffix input. No additional same-budget premise is imposed
on each factor inside the commutator. Future rewritten words must recheck their
own right suffixes; this draft does not claim one margin automatically covers
all arbitrary rewritten words.

Arbitrary boundary twist b occurs explicitly in `reconstructed_density_ccr`.
CH09's matching twisted inverse-Fourier dictionary identifies that integer-truncated
current with rho. This does **not** apply to `siteFourierDensity`, which has the
explicit wrapRemainder. The same-sea external energy offset β changes the physical
Hamiltonian by β times total number; charge-conserving transfers cancel β as already
proved in CH09. Budgets here retain the integer charge-sector excitation convention;
no twist-independent assertion about absolute energies or changing physical seas
is introduced.

The explicit example h=1,m=1,N=K=0 has a nonzero ground in its budget and
M1 predicts nonzero scalar action on that ground; this witnesses applicability
of the restricted identity itself. Existing nonzero ground kets and admissibility
witness inhabited natural budgets.
The empty occupation ket gives an explicit full-space commutator-zero test,
so the proposed global scalar mI equality is impossible for m>0, even at h=0.
The witness declarations below are stubs until Phase B; existing Core ground-ket
nonzero and budget-membership results are independently proved dependencies.

## Adopted, adapted and rejected ideas

- Adopted the source's one-particle edge calculation followed by the CAR Lie lift;
  this avoids circularly assuming the scalar CCR being established.
- Adopted explicit M1 occupation evaluation, M2 two-endpoint Pauli blocking,
  the normal-order scalar cancellation and right-suffix input margin.
- Adapted natural reference budgets to signed budgets only where intermediate
  negative word targets require them; negative spaces are handled as zero.
- Adapted the generic word sketch to existing exact-transfer and filtered-word APIs.
- Rejected an unrestricted global scalar CCR and a source-only bottom hop criterion.
- Rejected identifying cyclic site Fourier density with the nonwrapping current
  without its wrap remainder, and rejected abstract assumed oscillator CCR.

## Validation evidence

`lake build BosonizeStubs.A04CurrentMargins BosonizeStubs.Ch10Heisenberg`
passes (3394 jobs), with exactly the expected 37 sorry warnings across the pair
and no other warnings/errors. Native Lean MCP diagnostics on Ch10Heisenberg
returned complete successful elaboration, no failed dependencies, and 21 sorry
warnings only. Fresh data axiom audit reports only propext, Classical.choice and
Quot.sound (writtenExcursion has none); no data construction depends on sorryAx.
The theorem stubs of course are not proof-audited as completed.

The orchestrator's finite occupation screens h=1..4 verify 85 M1 instances and
184 unequal mixed M2 instances in `/tmp/bosonize-ch10/finite-screens.json`.
These are mathematical sanity screens, explicitly **not Lean proofs**.
Independent exact-source review and lock establishment remain pending.

## Exact Phase A source snapshot

```lean
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
```

## Reviewed Phase A gate

Independent reviewer `/root/ch10_interface_review`: PASS; see [review](../../../note/ch10_phase_a_review_2026-10-10.md). Root independently verified exact source mirrors, six standard-axiom data constructions, 37 expected one-sorry targets, successful Core and two-target staging build, and unchanged prior Core hashes. Only these two reviewed interface records were added. No theorem proof completion is asserted.

## Phase B complete — 2026-10-10

All theorem proofs are complete against reviewed baseline `e2074b4`; there are zero placeholders. Both library builds pass (3403 jobs), direct warning-as-error compilation is clean, native CH10 diagnostics return success with zero items and no failed dependencies, and fresh audits of all 37 theorems and six data declarations use only `propext`, `Classical.choice`, `Quot.sound`, or no axioms. The strict guard retains 616 statements and 478 commands. All fourteen pre-existing Core modules are unchanged.

A04 uses explicit finite edge bijections, interval coefficient arithmetic, concrete CAR occupation action and span induction. CH10 uses the sharper M1 separately from M2, handles signed negative budgets before natural casts, derives the signed commutator by cases, and tracks exact signed word targets before excursion enlargement. The empty-ket proof required an independently checked basis-normalization repair for differing equality instances; no signature was changed.

Proof groups: `/root/ch10_phase_a` (edge arithmetic), `/root/ch10_edge_probe` (span and Pauli blocking), `/root/ch10_interface_review` (signed CCR and witnesses), and `/root` (word/suffix maps and final troubleshooting/integration). Requested Flash/Pro tiers were unavailable; available inherited Codex models were used.

Phase B source SHA-256: `daa35798f941563bb5570eebbde98def16dbac32fc930c81337449e6f9893832`. The exact current source snapshot supersedes historical unproved Phase A descriptions above. Phase C promotion and pedagogical synchronization remain next.
