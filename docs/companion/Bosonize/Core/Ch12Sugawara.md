# Chapter 12 Sugawara: formal companion

Current status: all 26 proofs complete and promoted byte-identically to Core. Fresh post-promotion build, axiom and guard checks pass; complementary lecture review passes; Phase C is complete. The Phase A records below are historical snapshots.

Historical Phase A status: drafted, elaborated, and ready for independent mathematical/interface review. No statement below is proved in this staging file. There are 26 theorem contracts, each with exactly one `sorry`, and three complete noncomputable definitions plus two abbreviations. No separate A04 support module was needed. Existing Core and lock manifests were not edited.

## Sources and conventions

Reviewed `notes/md/ch12_Sugawara_construction.md` §§12.1–12.3, `notes/md/TOC.md`, `notes/appendices/a04_density_partitions_and_sugawara.md` (density, energy, completeness and Sugawara sections), and the current frozen CH11 source, including its actual lowering-through-word theorem and budget spanning theorem. Also checked CH05 integer Hamiltonians, CH07 integer excitation/ground-energy conventions, CH09 grading/physical Hamiltonian, CH10 restricted current algebra, the A04 dependency modules and the physical-energy section of CH06Ext. The dated `note/proof_suggestions_revision_2026-10-09.md` explicitly rejects natural charge and upper-M margins; these corrections are adopted. `docs/stub_suggestion/` and `docs/proof_suggestion/` do not exist in the current checkout, so no imagined suggestions or names were adopted.

The TOC's initial sentence that only Chapters 1–2 have completed Core is stale: the current repository supplies the compiled CH11 chain. The draft relies on current source contracts, not that historical status sentence. The actual Sugawara claims checked here are consistent with the finite carrier and accepted corrections; no unresolved physical-convention choice was discovered.

Flash/Pro model tools are unavailable in this session. This delegated Phase A task uses the inherited model as the explicitly authorized fallback. No nested agent was required for drafting. The parent must independently review before any scoped lock or Phase B transition.

## Carrier and complete data

`FockSpace h` is the actual concrete complex Euclidean occupation space on `Ch01.Band (2*h)`; operators are ambient `Module.End ℂ`. There is no invented bosonic certificate, replacement energy operator, or global finite CCR. `sugawaraHamiltonian h M` is literally the finite sum over `Finset.Icc 1 M` of `rho m * rho (-m)`. Multiplication is composition and the negative mode acts first. No bound M≤h−1 or M≤h is imposed.

`physicalRelativeHamiltonian` subtracts the energy of the frozen CH05 sea at the same real β from CH09's physical Hamiltonian. `physicalExcitationObservable` subtracts the corresponding real charge polynomial from that actual operator. The global cancellation contract is excitation-only; physical relative energy still has βN and absolute energy still has β times total occupation. To relate β to boundary fields, retain the CH06Ext choice `angleTwist (2*h) β`; CH09 already proves the matching reconstruction dictionary. CH12 adds no independent boundary choice or false absolute-energy independence.

All three definitions were audited after compilation with `#print axioms`: each depends only on `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` data dependency.

## Proof decomposition and margins

1. Finite-sum algebra: `sugawara_apply`, zero cutoff, actual adjoint and quadratic-form identity follow from finite linear-map sums, composition, and CH09's actual adjoint. Every summand is A†A for A=rho(-m); this gives positivity without an assumed state.
2. Cutoff stability: CH09's `rho_lowering_budget_zero` annihilates rho(-m) on B(N,K) whenever m>K. Apply this on the right before any CCR step. Split Icc 1 M into active m≤K and inactive m>K. These contracts need h>0 but no R2 and no upper-M margin. Ground action similarly uses `rho_lowering_ground` for all positive m.
3. Termwise action: first extend the frozen positive-list CH11 `lowering_through_word_erase` locally inside the proof, handling zero heads with the global number commutator; alternatively strip zeros, which contribute sector scalar h+N. The resulting local recurrence works under 0<m≤K and total energy≤K. Natural word parts may include zero; zero creators are rho_0 and contribute zero excitation. The frozen positive-list pull-through proof can be extended locally to zero entries using rho_number_commutator, without changing Core. Its right-remainder margin follows from m+n+E_remainder≤m+K≤2K. Restore the erased creator using `word_state_cons_erase`. If m is absent, its multiplicity is zero and both sides vanish. Global positive-mode commutativity restores the original word order without an extra left-prefix excursion.
4. Sum multiplicities: `positive_word_weight` is an arithmetic list counting lemma, independent of Fock/CCR. It states Σ_(1≤m≤K) m count(m)=parts.sum when the natural parts have total sum≤K. Zero parts contribute weight zero and require no positivity assumption. An induction on the list or a finite count-by-fiber identity is enough. Sum the termwise action at cutoff K, then use cutoff stability at arbitrary M≥K.
5. Partitions and whole budget: use CH11's positive partition lists and exact sum E, then the budget dependent labels `(E : Fin (K+1)) × Partition E`. `excitation_energy_space` is a separate span extension of CH07's diagonal ket action. Compare the two operators on every actual budget partition state and extend using `budget_partition_spanning`; no circular energy commutator is used for equivalence.
6. Relative integer energy: use the actual diagonal bridge `relative_hamiltonian_diagonal`, the identity excitation=relative−ground(charge), and fixed charge N on every budget ket. The integer division in `groundEnergy N` is exact because CH07 proves `ground_energy_double`; only then bridge to the complex polynomial N(N+1)/2. Negative N remains integer throughout.
7. Commutators: signed theorem has separate source K and target J, with K+n≤J, source/target R2 margins, and both K,J≤M. CH09 maps rho_n input to B(N,K+n), embedded in B(N,J), and proves global excitation covariance. Apply equivalence separately on input and shifted output, then subtract. The nonnegative wrapper uses J=K+n and its enlarged R2 margin; n=0 is valid, and the reference n>0 corollary is a special case. The theorem also permits lowering by choosing J=K, or a smaller dominating nonnegative target.
8. Physical dictionary: expand same-sea subtraction and use the fixed-charge diagonal action for βN; global excitation cancellation follows on occupation kets from CH06Ext's exact cancellation and CH07's divisibility bridge. Combine this with integer equivalence for physical relative energy. There is no analytic limit or unit-dependent 2π/L factor in this dimensionless linear-dispersion statement.
9. Nonvacuity: for excited witness use the actual vector rho_m vacuum, where 0<m≤K and 2K≤h ensure m≤h. CH09's direct sea norm theorem supplies nonzero action independently of Sugawara; grading gives membership, and word eigenvalue at N=0 gives eigenvalue m. The commutator witness uses vacuum in B(0,0), the same CH09 nonzero raising vector and the positive commutator wrapper with enlarged budget n. These are theorem obligations, not witnesses already proved in the new staging file.

## Validation evidence

`lake build BosonizeStubs.Ch12Sugawara` succeeded: 3397 jobs, exactly 26 expected declaration-uses-sorry warnings, no errors or linter warnings. Native Lean MCP `lean_diagnostic_messages` on the absolute source path with severity=error returned `partial=false`, `success=true`, empty items and no failed dependencies. The data audit described above succeeded through the installed compiler. `git diff --check` passed. Compilation with placeholders establishes only well-typed complete data and theorem headers; all 26 proofs remain Phase B obligations.

Live preflight quota was 19% five-hour remaining and 87% weekly remaining. Recheck before review/phase transition and obey the <10%/<5% checkpoint gate. The draft is unreviewed, unlocked and uncommitted; the parent owns review, locks and any next phase.

## Independent pre-review correction

The parent identified redundant positivity binders before interface freeze. Removed `hpos` from `density_bilinear_word`, `positive_word_weight`, and `sugawara_word_eigenvalue`; natural zero parts carry zero weight and their rho_0 factor preserves excitation. Removed `hn : 0<n` from `sugawara_raising_commutator`, since the n=0 identity also follows from the signed contract. No other theorem headers changed. Local proof treatment of zero word entries may use the existing global number commutator; the current frozen CH11 positive-list helper remains unchanged.

The correction batch began with 12% five-hour and 86% weekly allowance remaining.

## Exact elaborated theorem contracts

Source bodies each contain exactly one `sorry`.

```lean
lemma sugawara_zero (h : ℕ) : sugawaraHamiltonian h 0 = 0
```

```lean
lemma sugawara_apply (h M : ℕ) (v : FockSpace h) :
    sugawaraHamiltonian h M v =
      ∑ m ∈ Finset.Icc 1 M, Ch09.rho h (m : ℤ) (Ch09.rho h (-(m : ℤ)) v)
```

```lean
lemma sugawara_adjoint (h M : ℕ) :
    LinearMap.adjoint (sugawaraHamiltonian h M) = sugawaraHamiltonian h M
```

```lean
lemma sugawara_inner (h M : ℕ) (v : FockSpace h) :
    inner ℂ v (sugawaraHamiltonian h M v) =
      ∑ m ∈ Finset.Icc 1 M, inner ℂ (Ch09.rho h (-(m : ℤ)) v)
        (Ch09.rho h (-(m : ℤ)) v)
```

```lean
lemma sugawara_ground (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (M : ℕ) :
    sugawaraHamiltonian h M (Ch07.groundKet h N hN) = 0
```

```lean
lemma inactive_mode_zero (h : ℕ) (hh : 0 < h) (N : ℤ) (K m : ℕ)
    (hm : K < m) (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    (Ch09.rho h (m : ℤ) * Ch09.rho h (-(m : ℤ))) v = 0
```

```lean
lemma sugawara_cutoff_budget (h : ℕ) (hh : 0 < h) (N : ℤ) (K M : ℕ)
    (hM : K ≤ M) (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    sugawaraHamiltonian h M v = sugawaraHamiltonian h K v
```

```lean
lemma sugawara_cutoff_independent (h : ℕ) (hh : 0 < h) (N : ℤ) (K M M' : ℕ)
    (hM : K ≤ M) (hM' : K ≤ M') (v : FockSpace h)
    (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    sugawaraHamiltonian h M v = sugawaraHamiltonian h M' v
```

```lean
lemma density_bilinear_word (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K m : ℕ) (hm : 0 < m) (hmK : m ≤ K)
    (parts : List ℕ) (hE : parts.sum ≤ K)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    (Ch09.rho h (m : ℤ) * Ch09.rho h (-(m : ℤ))) (Ch11.wordState h N hN parts) =
      ((m*parts.count m : ℕ) : ℂ) • Ch11.wordState h N hN parts
```

```lean
lemma positive_word_weight (K : ℕ) (parts : List ℕ)
    (hE : parts.sum ≤ K) :
    ∑ m ∈ Finset.Icc 1 K, m*parts.count m = parts.sum
```

```lean
lemma sugawara_word_eigenvalue (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M : ℕ) (hM : K ≤ M)
    (parts : List ℕ) (hE : parts.sum ≤ K)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    sugawaraHamiltonian h M (Ch11.wordState h N hN parts) =
      (parts.sum : ℂ) • Ch11.wordState h N hN parts
```

```lean
lemma sugawara_partition_eigenvalue (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M E : ℕ) (hEK : E ≤ K) (hM : K ≤ M)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) (p : Nat.Partition E) :
    sugawaraHamiltonian h M (Ch11.partitionState h N hN p) =
      (E : ℂ) • Ch11.partitionState h N hN p
```

```lean
lemma excitation_energy_space (h : ℕ) (N E : ℤ) (v : FockSpace h)
    (hv : v ∈ Ch07.energySpace h N E) :
    Ch07.excitationObservable h v = (E : ℂ) • v
```

```lean
lemma excitation_partition_eigenvalue (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (E : ℕ) (p : Nat.Partition E) :
    Ch07.excitationObservable h (Ch11.partitionState h N hN p) =
      (E : ℂ) • Ch11.partitionState h N hN p
```

```lean
lemma sugawara_budget_partition_eigenvalue (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M : ℕ) (hM : K ≤ M)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) (p : Ch11.BudgetPartitions K) :
    sugawaraHamiltonian h M (Ch11.budgetPartitionState h N hN p) =
      (p.1.val : ℂ) • Ch11.budgetPartitionState h N hN p
```

```lean
theorem sugawara_equivalence (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M : ℕ) (hM : K ≤ M)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ))
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    Ch07.excitationObservable h v = sugawaraHamiltonian h M v
```

```lean
lemma relative_energy_budget (h : ℕ) (N : ℤ) (K : ℕ)
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    Ch05.shiftedHamiltonian (2*h) v =
      Ch07.excitationObservable h v + (Ch07.groundEnergy N : ℂ) • v
```

```lean
lemma ground_energy_complex (N : ℤ) :
    (Ch07.groundEnergy N : ℂ) = (N : ℂ)*((N : ℂ)+1)/2
```

```lean
theorem sugawara_relative_hamiltonian (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M : ℕ) (hM : K ≤ M)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ))
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    Ch05.shiftedHamiltonian (2*h) v =
      (sugawaraHamiltonian h M + ((N : ℂ)*((N : ℂ)+1)/2) • 1) v
```

```lean
theorem sugawara_signed_commutator (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K J M : ℕ) (n : ℤ)
    (hshift : (K : ℤ)+n ≤ (J : ℤ)) (hMK : K ≤ M) (hMJ : J ≤ M)
    (hsource : 2*(K : ℤ)+|N| ≤ (h : ℤ))
    (htarget : 2*(J : ℤ)+|N| ≤ (h : ℤ))
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    A02.commutator (sugawaraHamiltonian h M) (Ch09.rho h n) v =
      (n : ℂ) • Ch09.rho h n v
```

```lean
theorem sugawara_raising_commutator (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K M n : ℕ)
    (hM : K+n ≤ M) (hR2 : 2*((K+n : ℕ) : ℤ)+|N| ≤ (h : ℤ))
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    A02.commutator (sugawaraHamiltonian h M) (Ch09.rho h (n : ℤ)) v =
      (n : ℂ) • Ch09.rho h (n : ℤ) v
```

```lean
lemma physical_relative_budget (h : ℕ) (hh : 0 < h) (β : ℝ) (N : ℤ) (K : ℕ)
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    physicalRelativeHamiltonian h β v = Ch05.shiftedHamiltonian (2*h) v +
      ((β : ℂ)*(N : ℂ)) • v
```

```lean
lemma physical_excitation_cancel (h : ℕ) (hh : 0 < h) (β : ℝ) :
    physicalExcitationObservable h β = Ch07.excitationObservable h
```

```lean
theorem physical_sugawara_budget (h : ℕ) (hh : 0 < h) (β : ℝ) (N : ℤ)
    (hN : Ch07.admissible h N) (K M : ℕ) (hM : K ≤ M)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ))
    (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) :
    physicalRelativeHamiltonian h β v = sugawaraHamiltonian h M v +
      (Ch06Ext.physicalGroundEnergy β N : ℂ) • v
```

```lean
lemma sugawara_excited_witness (h : ℕ) (hh : 0 < h) (K M m : ℕ)
    (hm : 0 < m) (hmK : m ≤ K) (hM : K ≤ M) (hR2 : 2*K ≤ h) :
    ∃ v : FockSpace h, v ∈ Ch07.fixedBudget h 0 (K : ℤ) ∧ v ≠ 0 ∧
      sugawaraHamiltonian h M v = (m : ℂ) • v ∧ sugawaraHamiltonian h M v ≠ 0
```

```lean
lemma sugawara_commutator_witness (h : ℕ) (hh : 0 < h) (M n : ℕ)
    (hn : 0 < n) (hM : n ≤ M) (hR2 : 2*n ≤ h) :
    ∃ v : FockSpace h, v ∈ Ch07.fixedBudget h 0 0 ∧ v ≠ 0 ∧
      Ch09.rho h (n : ℤ) v ≠ 0 ∧
      A02.commutator (sugawaraHamiltonian h M) (Ch09.rho h (n : ℤ)) v ≠ 0
```

Draft source SHA-256: `948bd05acb85135c72a120ee4bd12daa3e3ebffaaf67715b27f8487002ca46e9`.

## Usage-gate handoff checkpoint

After the reviewed header cleanup, the final rebuild again succeeded with 3397 jobs and exactly 26 expected sorry warnings. The three-definition data axiom audit again reported only propext, Classical.choice and Quot.sound. Latest live quota is 9% five-hour remaining and 86% weekly remaining, so new drafting/proof work stops under the skill gate. Parent independent review is ongoing; the file remains Phase A, with 26 unproved obligations, unreviewed for final freeze, unlocked and uncommitted. Resume after the usage gate permits, beginning with final independent review and scoped lock, never infer Phase B completion from this build.

## Final independent review and scheduled continuation

The [independent final-source review](../../../../note/ch12_phase_a_review_2026-10-11.md) is PASS. This supersedes the preceding in-progress review status; the source remains exactly the reviewed SHA above. The draft is checkpointed while still unlocked and wholly unproved because the five-hour allowance reached 9%. The [durable quota checkpoint](../../../../note/quota_checkpoint_2026-10-11_ch12.md) records the scheduled continuation and exact next action. Before initial locking on recovery, refresh the current source/data audit including both abbreviations, then establish only this reviewed module's interface. Existing Core remains unchanged.

## Fresh reset validation and reviewed interface freeze

On October 11, after 18:14 UTC, the five-hour allowance recovered to 98% remaining and weekly to 85%. The consumed wakeup was deleted; no reset or paid credits were used. The exact reviewed Lean SHA remains `948bd05acb85135c72a120ee4bd12daa3e3ebffaaf67715b27f8487002ca46e9`. Fresh targeted Lake build passed 3397 jobs with exactly the 26 expected theorem-placeholder warnings. Native Lean MCP diagnostics completed with those same 26 warnings, zero errors and no failed dependencies. Fresh axiom inspection of all five complete data declarations, including both abbreviations, reports only `propext`, `Classical.choice`, `Quot.sound`. The eighteen existing complete-source Core hashes and 677 existing theorem interfaces passed their guards. New upstream LaTeX/workflow commits do not alter this reviewed source, its reference Markdown or Core.

Only this reviewed CH12 interface is added to the current manifest and staging aggregator. Its mathematical review is recorded in [the independent report](../../../../note/ch12_phase_a_review_2026-10-11.md). Phase B now supplies all 26 obligations; placeholders still represent unproved targets. Sectional proving uses available inherited Codex agents because Flash/Pro tools are not exposed in this session.

## Complete Phase B proof evidence

All 26 reviewed targets now have complete proof bodies; the five data declarations remain unchanged. Source SHA-256: `24bd8be1167243715b3c4b50d55917581599facdfabf3b53111669b32619bcab`. The complete source passes direct warning-as-error elaboration and the 3397-job targeted build without warnings. Native MCP returns complete empty diagnostics and no failed dependencies. Fresh inspection of all 31 declarations confirms only the three permitted standard axioms; see [audit](../../../../note/ch12_phase_b_axiom_audit_2026-10-11.json).

The local natural-list pull-through handles zero entries with the actual signed current relation on each right suffix; it does not weaken or modify the frozen CH11 positive-list helper. Inactive modes vanish by grading before any current relation is invoked. Multiplicity-weight action and the partition spanning theorem establish whole-budget equivalence before its commutator corollary. Separate source and target margins are retained. The physical dictionary keeps the same-sea βN shift and exact charge-dependent ground polynomial, with global excitation cancellation after subtracting that polynomial. Both witnesses use independently proved nonzero sea-density action. Sectional scratch dependency placeholders were eliminated by integration and the fresh complete transitive audit. No mathematical interface correction or Core edit was needed.

Sectional proof authors: `/root/ch11_phase_a` (finite identities), `/root/ch11_gram_probe` (word action), `/root/ch12_phase_a` (physical energy), `/root` (budget equivalence, commutators and witnesses). Proof-suggestion directories are absent in the current checkout; prior companion source reconciliation and actual installed Core APIs guide the proofs. Independent proof/promotion review and full CI evidence follow before promotion.

Independent integrated review: [PASS report](../../../../note/ch12_phase_b_review_2026-10-11.md), exact final SHA above. Reviewer disclosure records the six energy proofs it authored; the root independently inspected those bodies, while the reviewer scrutinized the other twenty. Full Phase B CI passes 69 guard tests, strict 703-statement/526-command interface verification, eighteen unchanged Core hashes and both library builds (Core 3403 jobs, staging 3405 jobs). An initial aggregator import-position error was journaled and corrected before this passing run.

## Phase C migration and validation

Phase B commit: `3019689`; interface baseline: `f631d5b`. Independent migration review approved a byte-identical move to `Bosonize/Core/Ch12Sugawara.lean`; no import substitution was needed. The exact v2 record moves by path unchanged, and the Core manifest adds only this source hash. All eighteen older Core modules remain byte-identical. See [migration evidence](../../../../note/ch12_phase_c_migration_2026-10-11.json).

Post-promotion CI passes 69 guard tests, 703 frozen theorem statements/526 commands, nineteen complete-source hashes, Core build 3404 jobs and staging build 3405 jobs, without warnings. Fresh Core-aggregator axiom inspection of all 31 declarations matches the staging audit and contains only the standard axioms; [Core audit](../../../../note/ch12_phase_c_axiom_audit_2026-10-11.json). Native MCP diagnostics on the promoted source complete with empty diagnostics and no failed dependencies. No placeholders remain.

The corresponding lecture is `notes/md/ch12_Sugawara_construction.md`; the remaining A04 Sugawara support is explained in `notes/appendices/a04_density_partitions_and_sugawara.md`. This support is implemented in CH12 itself, not a newly invented appendix module. The notes retain reference formulas and earlier proposed strategies while adding the actual finite construction. Independent pedagogical review evidence follows.

## Exact completed Core source

```lean
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

```

Independent pedagogical review by `/root/ch11_gram_probe`: [unconditional PASS](../../../../note/ch12_phase_c_pedagogical_review_2026-10-11.md). The original CH12 reference remains an exact prefix and original display formulas in both notes are preserved. Final Core links, completion wording and section anchors pass review. KaTeX validation covers 34 notes/3224 math fragments with no errors; [validation](../../../../note/ch12_phase_c_markdown_validation_2026-10-11.json). [Final Phase C evidence](../../../../note/ch12_phase_c_validation_2026-10-11.md).
