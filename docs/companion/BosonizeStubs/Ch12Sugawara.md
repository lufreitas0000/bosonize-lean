# Chapter 12 Sugawara: formal companion

Current status: all 26 proofs complete, warning-free targeted builds and fresh 31-declaration standard-axiom audit pass; independent review and Phase C validation are in progress. The Phase A records below are historical snapshots.

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

The [independent final-source review](../../../note/ch12_phase_a_review_2026-10-11.md) is PASS. This supersedes the preceding in-progress review status; the source remains exactly the reviewed SHA above. The draft is checkpointed while still unlocked and wholly unproved because the five-hour allowance reached 9%. The [durable quota checkpoint](../../../note/quota_checkpoint_2026-10-11_ch12.md) records the scheduled continuation and exact next action. Before initial locking on recovery, refresh the current source/data audit including both abbreviations, then establish only this reviewed module's interface. Existing Core remains unchanged.

## Fresh reset validation and reviewed interface freeze

On October 11, after 18:14 UTC, the five-hour allowance recovered to 98% remaining and weekly to 85%. The consumed wakeup was deleted; no reset or paid credits were used. The exact reviewed Lean SHA remains `948bd05acb85135c72a120ee4bd12daa3e3ebffaaf67715b27f8487002ca46e9`. Fresh targeted Lake build passed 3397 jobs with exactly the 26 expected theorem-placeholder warnings. Native Lean MCP diagnostics completed with those same 26 warnings, zero errors and no failed dependencies. Fresh axiom inspection of all five complete data declarations, including both abbreviations, reports only `propext`, `Classical.choice`, `Quot.sound`. The eighteen existing complete-source Core hashes and 677 existing theorem interfaces passed their guards. New upstream LaTeX/workflow commits do not alter this reviewed source, its reference Markdown or Core.

Only this reviewed CH12 interface is added to the current manifest and staging aggregator. Its mathematical review is recorded in [the independent report](../../../note/ch12_phase_a_review_2026-10-11.md). Phase B now supplies all 26 obligations; placeholders still represent unproved targets. Sectional proving uses available inherited Codex agents because Flash/Pro tools are not exposed in this session.

## Complete Phase B proof evidence

All 26 reviewed targets now have complete proof bodies; the five data declarations remain unchanged. Source SHA-256: `24bd8be1167243715b3c4b50d55917581599facdfabf3b53111669b32619bcab`. The complete source passes direct warning-as-error elaboration and the 3397-job targeted build without warnings. Native MCP returns complete empty diagnostics and no failed dependencies. Fresh inspection of all 31 declarations confirms only the three permitted standard axioms; see [audit](../../../note/ch12_phase_b_axiom_audit_2026-10-11.json).

The local natural-list pull-through handles zero entries with the actual signed current relation on each right suffix; it does not weaken or modify the frozen CH11 positive-list helper. Inactive modes vanish by grading before any current relation is invoked. Multiplicity-weight action and the partition spanning theorem establish whole-budget equivalence before its commutator corollary. Separate source and target margins are retained. The physical dictionary keeps the same-sea βN shift and exact charge-dependent ground polynomial, with global excitation cancellation after subtracting that polynomial. Both witnesses use independently proved nonzero sea-density action. Sectional scratch dependency placeholders were eliminated by integration and the fresh complete transitive audit. No mathematical interface correction or Core edit was needed.

Sectional proof authors: `/root/ch11_phase_a` (finite identities), `/root/ch11_gram_probe` (word action), `/root/ch12_phase_a` (physical energy), `/root` (budget equivalence, commutators and witnesses). Proof-suggestion directories are absent in the current checkout; prior companion source reconciliation and actual installed Core APIs guide the proofs. Independent proof/promotion review and full CI evidence follow before promotion.

Independent integrated review: [PASS report](../../../note/ch12_phase_b_review_2026-10-11.md), exact final SHA above. Reviewer disclosure records the six energy proofs it authored; the root independently inspected those bodies, while the reviewer scrutinized the other twenty. Full Phase B CI passes 69 guard tests, strict 703-statement/526-command interface verification, eighteen unchanged Core hashes and both library builds (Core 3403 jobs, staging 3405 jobs). An initial aggregator import-position error was journaled and corrected before this passing run.
