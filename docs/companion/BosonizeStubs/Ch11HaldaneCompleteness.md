# CH11 Haldane completeness — Phase A companion

This is a reviewed-interface candidate on actual fermionic density states. Gram, nonzero states, finite counting and completeness remain unproved. The file includes no CH12/Sugawara work and preserves upstream Core.

Sources: `notes/md/ch11_Haldane_completeness.md`, `notes/md/TOC.md`, `notes/appendices/a04_density_partitions_and_sugawara.md`, and historical P06/P07 in `note/proof_suggestions_revision_2026-10-09.md`. Suggestions directories are absent. Adopted: actual positive current products, finite rectangle bijection, Hall factor, right-remainder R2 induction. Adapted: use the installed `Module.Basis` namespace and existential basis theorem with exact vector equations, avoiding a data definition depending on a placeholder membership proof. Rejected: generic commutative endomorphism products, global scalar CCR, assumed Gram/dimension/spanning certificates, and replacing density states with coordinate kets. Flash/Pro providers are unavailable; the drafting agent uses its inherited available model.

The state is the written-order list product of CH09's actual finite density operators applied to CH07's actual admissible ground ket. The rightmost operator acts first. A descending sort chooses a representative of the positive partition multiset, and global same-sign commutativity proves permutation independence. This does not alter the reference sea or choose a new physical twist. `hallFactor` is the exact natural product `∏ m, m^(count m) * (count m)!`; casts yield the complex Gram coefficient. No inner product is replaced by a synthetic algebraic pairing.

Fixed-energy membership uses exact grading, not only a filtered upper bound. `creator_word_exact_shift` is the induction contract needed for that distinction. The full budget index is the dependent sum of `Fin(K+1)` energies and partitions of each energy; it includes the unique zero-energy ground.

The local pull-through invariant is exposed in `remainder_ccr`, `right_remainder_margin` and `lowering_cons`: with remainder energy E = parts.sum and n+E≤K, the margin m+n+E+|N|≤m+K+|N|≤2K+|N| holds. The already traversed left prefix contributes no extra energy because the restricted CCR acts on the right remainder. The diagonal commutator orientation is `[rho(-m),rho(m)] = +m`; off-diagonal terms vanish. No global finite-dimensional scalar CCR is claimed. Both an occurrence sum with `eraseIdx` and a consolidated multiplicity formula with `erase` are exposed for downstream contraction/Gram use.

Proof dependency plan:

1. List/multiset order and recurrence helpers; exact grading and energy/budget membership via CH09 rho_exact_shift and CH07 ground energy.
2. Local remainder CCR from CH10 rho_signed_ccr, arithmetic R2 margin, and lowering_cons. Induct the positive creator word, annihilating the final ground with CH09 rho_lowering_ground; consolidate matching occurrences using word_state_cons_erase.
3. Transfer a left creator to a right lowering operator using actual Hilbert adjoint rho_adjoint. Ground-ground inner product is one; positive-energy ground-word inner product vanishes by coordinate orthogonality. Prove Hall factor positivity and factorial recurrence.
4. Induct word Gram with erase/count contraction; equality of multisets characterizes the diagonal. Specialize to partitions, prove nonzero states and linear independence. Different-energy budget blocks are orthogonal; dependent pair equality handles their labels.
5. Derive R1 from R2, obtain finrank from A04's explicit occupation-partition equivalence, and use linear independence plus equal cardinality to establish fixed-energy spanning and a `Module.Basis` whose coerced vectors are the actual states. Installed `basisOfLinearIndependentOfCardEqFinrank'` is the intended construction after checking subtype linear independence.
6. Assemble whole budget spanning via A03.budget_energy_decomposition and CH07 excitation_nonneg. Combine orthogonality/nonzero norms for independence, then construct the budget basis from proved membership, independence and spanning. The existence statements characterize every vector and do not supply certificates as assumptions.

Every theorem/lemma currently has exactly one `by sorry`. A successful build establishes elaboration only. No locks, commits or promotions are performed by this drafting agent.

Validation snapshot (2026-10-11):

- Source SHA-256: `dc47b114e7e53dade84084fbca1ad500c6b70b7fc1f785fc42ec6ceff86693fd`.
- 36 theorem/lemma declarations, 36 expected placeholders; all theorem bodies satisfy the single-sorry contract.
- 8 complete data/abbreviation declarations. Fresh `#print axioms` for all 15 data declarations across both modules reports only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- `lake build BosonizeStubs.A04PartitionCombinatorics BosonizeStubs.Ch11HaldaneCompleteness` succeeds with expected staging sorry warnings only.
- Native Lean MCP error diagnostics for CH11 succeeded with complete, nonpartial empty error results. This is elaboration evidence, not proof completion.

Exact proposed signatures:

```lean
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

lemma lowering_cons (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : Ch07.admissible h N)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (parts : List ℕ)
    (hmargin : (m : ℤ)+(n : ℤ)+(parts.sum : ℤ)+|N| ≤ (h : ℤ)) :
    Ch09.rho h (-(m : ℤ)) (wordState h N hN (n::parts)) =
      Ch09.rho h (n : ℤ) (Ch09.rho h (-(m : ℤ)) (wordState h N hN parts)) +
        (if m=n then (m : ℂ) else 0) • wordState h N hN parts := by sorry

lemma lowering_through_word (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K m : ℕ) (hm : 0 < m) (hmK : m ≤ K)
    (parts : List ℕ) (hpos : ∀ n ∈ parts, 0 < n) (hE : parts.sum ≤ K)
    (hR2 : 2*(K : ℤ)+|N| ≤ (h : ℤ)) :
    Ch09.rho h (-(m : ℤ)) (wordState h N hN parts) =
      ∑ i : Fin parts.length,
        if parts[i] = m then (m : ℂ) • wordState h N hN (parts.eraseIdx i.val) else 0 := by sorry

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

```

## Phase B integration and scoped interface review

All theorem bodies are complete. Initial reviewed baseline: `c788bb3`. The [independent proof and migration review](../../../note/ch11_phase_b_review_2026-10-11.md) approved dropping only the redundant positive-size hypothesis of `inverse_displacement_parts`; its geometric recovery proof also covers the empty h=0 case. The sole caller was adjusted; every other header, data declaration and existing Core file is unchanged. The signatures above are the historical Phase A snapshot. Fresh whole-module builds and all-declaration axiom audits precede promotion.

Independent cross-review also removed the redundant positivity premises from `hall_factor_cons`. The recurrence now holds for every natural multiset; positivity remains required separately for nonzero Hall norms and the physical positive-part Gram theorem. The proof uses direct factor splitting, count and factorial identities, without an artificial cancellation step. All 36 CH11 targets were freshly audited on the exact reviewed candidate with permitted axioms only.
