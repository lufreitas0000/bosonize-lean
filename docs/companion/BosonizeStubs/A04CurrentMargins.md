# A04CurrentMargins: formal companion

Phase A draft, 2026-10-10. Independent Phase A review passed; the reviewed interface is now locked.
Phase B proofs are pending. **16 theorem stubs, each exactly one `by sorry`**, three fully elaborated
data constructions. Source SHA-256: `fd9f539abd4e4026531e007ee79f7c9f88e3a13f6b67c522bda26563f19356d2`. The exact snapshot below records all
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
```

## Reviewed Phase A gate

Independent reviewer `/root/ch10_interface_review`: PASS; see [review](../../../note/ch10_phase_a_review_2026-10-10.md). Root independently verified exact source mirrors, six standard-axiom data constructions, 37 expected one-sorry targets, successful Core and two-target staging build, and unchanged prior Core hashes. Only these two reviewed interface records were added. No theorem proof completion is asserted.

## Phase B complete — 2026-10-10

All theorem proofs are complete against reviewed baseline `e2074b4`; there are zero placeholders. Both library builds pass (3403 jobs), direct warning-as-error compilation is clean, native CH10 diagnostics return success with zero items and no failed dependencies, and fresh audits of all 37 theorems and six data declarations use only `propext`, `Classical.choice`, `Quot.sound`, or no axioms. The strict guard retains 616 statements and 478 commands. All fourteen pre-existing Core modules are unchanged.

A04 uses explicit finite edge bijections, interval coefficient arithmetic, concrete CAR occupation action and span induction. CH10 uses the sharper M1 separately from M2, handles signed negative budgets before natural casts, derives the signed commutator by cases, and tracks exact signed word targets before excursion enlargement. The empty-ket proof required an independently checked basis-normalization repair for differing equality instances; no signature was changed.

Proof groups: `/root/ch10_phase_a` (edge arithmetic), `/root/ch10_edge_probe` (span and Pauli blocking), `/root/ch10_interface_review` (signed CCR and witnesses), and `/root` (word/suffix maps and final troubleshooting/integration). Requested Flash/Pro tiers were unavailable; available inherited Codex models were used.

Phase B source SHA-256: `48119166b886ffd0a92c79111570142d931467d089aa1e777c1bab9b466ffd16`. The exact current source snapshot supersedes historical unproved Phase A descriptions above. Phase C promotion and pedagogical synchronization remain next.
