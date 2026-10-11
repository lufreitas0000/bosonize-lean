# A05 multispecies support: Phase A companion

Status: Phase B complete: all 28 theorem proofs and all supporting data are freshly standard-axiom audited. Zero warnings/placeholders. Phase C promotion and complementary pedagogical synchronization are pending; no Core promotion is claimed.

Sources: `notes/md/ch13_Klein_factors.md`, `notes/appendices/a05_exponentials_klein_and_vertex_scope.md`, the CH13 TOC entry, applicable restricted-map/tensor-budget/phase corrections in `note/proof_suggestions_revision_2026-10-09.md`, and current frozen CH07, CH11, CH04/A02, CH09 and CH06Ext contracts. Historical brainstorm/API suggestions are advisory; nonexistent `docs/stub_suggestion/` and `docs/proof_suggestion/` were not invented. The A05 exponential and CH14 vertex research sections are excluded from this chapter: this draft asserts no unprojected vertex equality or analytic exponential.

The dedicated drafting agent uses the inherited Codex model because Flash/Pro tools are not exposed. Formalizer and active-focus skills were reread; ACTIVE_FOCUS permits the expressly authorized CH13 scope and does not authorize unrelated Icebox Luther–Emery work. Current workspace state was inspected. Actual API/reducibility and zero-mode failures were journaled before correction in `LOG_DISCOVERY_AND_PIVOTS.md`.

The ordinary product `σ × Band(2*h)` is retained, so these are actual CH07 occupation/budget carriers. `speciesOrder` supplies the lexical total order through the definitionally identical wrapper; four NAMED LOCAL projections (LinearOrder, LT, LE, DecidableEq) are installed explicitly in each module. No global product order instance is exported. This avoids the product componentwise LT or default DecEq silently overriding CAR conventions. The local constants are included in the complete-data axiom audit.

## Complete data and actual carriers

This support is a prerequisite to CH13; it does not extend the A05 exponential/vertex scope. `jointBudget h Ns K` is exactly frozen `Ch07.speciesBudget h Ns (K:ℤ)`: every actual configuration has each specified charge and SUMMED excitation ≤K. It is not the tensor product of independently cut-off species budgets. The label `JointPartitions σ K` is a tuple of actual `(Eν:Fin(K+1), Partition Eν)` labels constrained by ΣEν≤K. Individual finite cutoff K merely enumerates the possible split coordinates; the subtype enforces the physical total bound.

`jointConfiguration` joins actual species occupations; `groundConfiguration` joins frozen single-species ground configurations. `tensorVector` is the coordinate product on this same actual fermionic carrier, with coefficients ∏ν vν(fiberν S), transported by the frozen coordinate equivalence. This is a complete finite vector definition, not an abstract coefficient carrier substituted for the physical budget. `wordState` is independently defined by actual full-space CAR density products acting on the actual joint ground ket. Its equality with the product of single-species CH11 words is an explicit theorem obligation (`word_tensor`).

The annihilation/creation operators are actual CH04 operators for the chosen lexical order. `rho` is the finite valid-pair sum of full-space same-species hoppings, retaining no-wrap integer momentum transfers. `liftedAnnihilation` uses the exact CH06Ext twisted character and frozen normalization with a SPECIES FAMILY bν. Klein maps later have no independent twist argument because they are sector/current maps; physical field comparisons retain this family in their ground matrix coefficient. This is not absolute energy or arbitrary-dispersion twist independence.

## Dependency order and proof design

1. Prove the lexical comparison law, joint/fiber inverse identities, and coordinate product ket/inner formulas. Reviewer feasibility probes compiled an actual combined-occupation equivalence with inverse by biUnion/image, and an optional algebraic tensor basis transport. These probes show the route is viable; their proved scratch results are not incorporated as Phase B completion here. The simpler coordinate product avoids unnecessary tensor imports.
2. Prove `preceding_count_split` on actual occupations. An odd annihilator has preceding-species parity; it must never be identified with an ungraded tensor factor. For the even hop, both CAR factors carry the same preceding-species parity, whose square is one. This supplies `hopping_tensor`, then `rho_tensor`. Cross-species density commutation separately follows actual CAR bilinear commutators with distinct first coordinates. Zero-transfer density remains the actual species particle count.
3. Use `tensor_kets` plus actual even density factor action to prove `word_tensor`; repeated same-species creators and the sorted species product agree on the concrete carrier. No equality of current/Gram factors follows from bare carrier equivalence alone.
4. Prove total-energy grading, lowering annihilation below the nonnegative excitation floor, actual ground/word/partition budget membership, and actual nonzero ground ket. These need h>0/admissibility where stated but no scalar CCR margin.
5. Under per-species R2, use frozen CH11 word/partition Gram and `tensor_inner` to derive the product Gram factor `jointNormalization`. Distinct joint labels differ in at least one actual energy/partition coordinate, yielding orthogonality; normalization is a positive product of frozen positive Hall factors.
6. For whole-budget spanning, expand an actual joint occupation ket S. Each fiber has nonnegative exact energy eν; Σeν≤K. Apply frozen `Ch11.fixed_energy_basis` to that fiber's `Ch07.energySpace` at eν, since eν≤K supplies its R2 margin. Expand the coordinate product multilinearly. Every resulting label has exact split eν and total≤K, hence belongs to `JointPartitions`. This proves the ACTUAL total-budget span; a box-dimension count cannot substitute for this step. Independence follows the Gram formula, giving the typed actual budget basis.
7. `charge_budget` follows fixed coordinate charges, supporting the later typed number shift.

No current coefficient, surjectivity, or factorization is assumed as a data certificate. All these are explicit Phase B obligations below.

## Validation and exact interface

The combined target build passed 3398 jobs with exactly 53 expected sorry warnings (A05:28, CH13:25); no errors or non-sorry warnings. Native CH13 error diagnostics completed with partial=false, success=true, empty items and no failed dependencies. Fresh data audit covers all 42 named data/abbreviation/instance constants, INCLUDING the eight local order projections; only standard axioms are permitted and no sorryAx data dependency occurs. See `note/ch13_phase_a_data_axiom_audit_2026-10-11.json` for the source-bound audit. That historical Phase A build establishes data/header elaboration only. Current partial proof evidence is recorded below.

Source SHA-256: `320d0252816ec01dff10de1a6e3d7f76a80c7c9e3276043c3c6ea29c6f04a092`.

```lean
omit [Fintype σ] in
lemma mode_lt_iff (h : ℕ) (ν η : σ) (k l : Ch01.Band (2*h)) :
    (ν,k) < (η,l) ↔ ν < η ∨ ν=η ∧ k<l
```

```lean
lemma species_joint_configuration (h : ℕ) (Ss : σ → Ch07.Occupation h) (ν : σ) :
    Ch07.speciesConfiguration h (jointConfiguration h Ss) ν = Ss ν
```

```lean
lemma joint_species_configuration (h : ℕ) (S : Occupation σ h) :
    jointConfiguration h (fun ν => Ch07.speciesConfiguration h S ν) = S
```

```lean
lemma tensor_kets (h : ℕ) (Ss : σ → Ch07.Occupation h) :
    tensorVector h (fun ν => A02.ket (Ss ν)) = A02.ket (jointConfiguration h Ss)
```

```lean
lemma tensor_inner (h : ℕ) (vs ws : σ → Ch07.FockSpace h) :
    inner ℂ (tensorVector h vs) (tensorVector h ws) = ∏ ν, inner ℂ (vs ν) (ws ν)
```

```lean
lemma rho_tensor (h : ℕ) (ν : σ) (m : ℤ) (vs : σ → Ch07.FockSpace h) :
    rho h ν m (tensorVector h vs) =
      tensorVector h (Function.update vs ν (Ch09.rho h m (vs ν)))
```

```lean
lemma word_tensor (h : ℕ) (Ns : σ → ℤ) (hN : admissible h Ns) (parts : σ → List ℕ) :
    wordState h Ns parts = tensorVector h (fun ν => Ch11.wordState h (Ns ν) (hN ν) (parts ν))
```

```lean
lemma annihilation_car (h : ℕ) (i j : Mode σ h) :
    A02.anticommutator (annihilation h i.1 i.2) (annihilation h j.1 j.2) = 0
```

```lean
lemma creation_car (h : ℕ) (i j : Mode σ h) :
    A02.anticommutator (creation h i.1 i.2) (creation h j.1 j.2) = 0
```

```lean
lemma mixed_car (h : ℕ) (i j : Mode σ h) :
    A02.anticommutator (annihilation h i.1 i.2) (creation h j.1 j.2) =
      (if i=j then (1 : ℂ) else 0) • (1 : Operators σ h)
```

```lean
lemma hopping_tensor (h : ℕ) (ν : σ) (p k : Ch01.Band (2*h)) (vs : σ → Ch07.FockSpace h) :
    Ch04.hopping (ν,p) (ν,k) (tensorVector h vs) =
      tensorVector h (Function.update vs ν (Ch04.hopping p k (vs ν)))
```

```lean
lemma preceding_count_split (h : ℕ) (ν : σ) (k : Ch01.Band (2*h)) (S : Occupation σ h) :
    Ch04.precedingCount (ν,k) S =
      (∑ η ∈ Finset.univ.filter (· < ν), (Ch07.speciesConfiguration h S η).card) +
        Ch04.precedingCount k (Ch07.speciesConfiguration h S ν)
```

```lean
lemma creation_adjoint (h : ℕ) (ν : σ) (k : Ch01.Band (2*h)) :
    LinearMap.adjoint (annihilation h ν k) = creation h ν k
```

```lean
lemma rho_adjoint (h : ℕ) (ν : σ) (m : ℤ) :
    LinearMap.adjoint (rho h ν m) = rho h ν (-m)
```

```lean
lemma rho_cross_commute (h : ℕ) (ν η : σ) (hne : ν ≠ η) (m n : ℤ) :
    A02.commutator (rho h ν m) (rho h η n) = 0
```

```lean
lemma rho_positive_commute (h : ℕ) (ν : σ) (m n : ℕ) :
    A02.commutator (rho h ν (m : ℤ)) (rho h ν (n : ℤ)) = 0
```

```lean
lemma rho_budget_map (h : ℕ) (ν : σ) (m : ℤ) (Ns : σ → ℤ) (K : ℕ)
    (v : FockSpace σ h) (hv : v ∈ jointBudget h Ns K) :
    rho h ν m v ∈ Ch07.speciesBudget h Ns ((K : ℤ)+m)
```

```lean
lemma rho_lowering_budget_zero (h : ℕ) (hh : 0 < h) (ν : σ) (m K : ℕ)
    (hm : K < m) (Ns : σ → ℤ) (v : FockSpace σ h) (hv : v ∈ jointBudget h Ns K) :
    rho h ν (-(m : ℤ)) v = 0
```

```lean
lemma ground_mem_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : admissible h Ns) (K : ℕ) :
    groundKet h Ns ∈ jointBudget h Ns K
```

```lean
lemma ground_ne_zero (h : ℕ) (Ns : σ → ℤ) : groundKet h Ns ≠ 0
```

```lean
lemma word_mem_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : admissible h Ns)
    (parts : σ → List ℕ) (K : ℕ) (hE : ∑ ν, (parts ν).sum ≤ K) :
    wordState h Ns parts ∈ jointBudget h Ns K
```

```lean
lemma partition_mem_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : admissible h Ns) (K : ℕ) (p : JointPartitions σ K) :
    partitionState h Ns p ∈ jointBudget h Ns K
```

```lean
omit [LinearOrder σ] in
lemma joint_normalization_positive (K : ℕ) (p : JointPartitions σ K) :
    0 < jointNormalization p
```

```lean
lemma partition_gram (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : admissible h Ns) (K : ℕ) (hR2 : r2 h K Ns) (p q : JointPartitions σ K) :
    inner ℂ (partitionState h Ns p) (partitionState h Ns q) =
      if p=q then (jointNormalization p : ℂ) else 0
```

```lean
lemma partition_ne_zero (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : admissible h Ns) (K : ℕ) (hR2 : r2 h K Ns) (p : JointPartitions σ K) :
    partitionState h Ns p ≠ 0
```

```lean
lemma partition_spanning (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : admissible h Ns) (K : ℕ) (hR2 : r2 h K Ns) :
    Submodule.span ℂ (Set.range (partitionState h Ns (K := K))) = jointBudget h Ns K
```

```lean
lemma partition_basis (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : admissible h Ns) (K : ℕ) (hR2 : r2 h K Ns) :
    ∃ b : Module.Basis (JointPartitions σ K) ℂ (jointBudget h Ns K),
      ∀ p, (b p : FockSpace σ h) = partitionState h Ns p
```

```lean
lemma charge_budget (h : ℕ) (ν : σ) (Ns : σ → ℤ) (K : ℕ)
    (v : FockSpace σ h) (hv : v ∈ jointBudget h Ns K) :
    chargeObservable h ν v = (Ns ν : ℂ) • v
```

## Root exact-source verification

Fresh root inspection independently audits all 42 complete data declarations, including the eight local order projections, with standard axioms only. Native diagnostics on both final source files complete with exactly their 28/25 expected placeholder warnings, zero errors and no failed dependencies. Existing nineteen Core hashes pass against `c3169bf`. Root mathematical review confirms total-energy rather than box budgets, actual lexical CAR, even-hop parity cancellation, genuine product Gram normalization, matching source-conjugate inverse, both typed inverse directions, strict positive-mode squares, the separate number law, and the retained species twist in the physical ground-to-ground coefficient.

An independent finite integer-parity oracle checks 1384 ground top-mode removals and 2176 ordered cross-species phase pairs for h=1,2,3 and one to three species, across admissible negative and positive charges. These finite checks support review and are not Lean proofs or a substitute for the universal phase obligations.

## Reviewed interface freeze

Independent author-distinct review by `/root/ch11_gram_probe`: [PASS](../../../note/ch13_phase_a_review_2026-10-11.md), tied to the final source hash above. All previous manifest records remain identical; only the two reviewed staging entries are added. The committed baseline authorizes proof-body replacements only. All 53 obligations remain unproved at freeze; promotion requires complete proofs, fresh audits and independently reviewed complementary lectures.

## Phase B partial checkpoint — 2026-10-11

Completed and freshly standard-axiom audited: `tensor_kets`, `mode_lt_iff`, `species_joint_configuration`, `joint_species_configuration`, `annihilation_car`, `creation_car`, `mixed_car`, `creation_adjoint`, `ground_ne_zero`, `ground_mem_budget`, `joint_normalization_positive`, `charge_budget`. No completed theorem depends on `sorryAx`. The integrated two-module build passes 3398 jobs with exactly 37 warnings for remaining placeholders and no other warnings. Full Phase B and Phase C are pending. See [partial audit](../../../note/ch13_phase_b_partial_audit_2026-10-11.json) and [reviewed instance cleanup](../../../note/ch13_unused_instance_amendment_review_2026-10-11.md). The Phase A source hash above is historical; the current source hash is in the partial audit.

## Complete Phase B audit — 2026-10-11

The current source SHA-256 is `bb9055adcf9358d5f2274666205d31dc3073716fe53e5f6bf02a983f92335bc2`. All 53 combined theorem proofs and 42 data declarations pass the fresh 95-declaration axiom audit, using only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Both modules pass direct warning-as-error compilation and the 3398-job combined build. Native diagnostics are complete with no warnings/errors/failed dependencies; CH13 has one informational tactic suggestion only. Strict guard verifies 756 statements/588 commands; 69 guard tests pass. Existing nineteen Core sources remain unchanged. Historical Phase A/partial checkpoint counts above are retained as history and superseded by this complete audit.

The implemented proof uses actual occupation configurations and coordinate products, with local multilinearity extending ket identities. Earlier-species parity occurs twice in an even hop and cancels. Total-budget spanning uses dependent fixed-energy bases at the actual fiber energies; only joined labels whose summed energy is at most K enter the span. It does not use a product of independently capped budgets.

Fresh evidence: [axiom audit](../../../note/ch13_phase_b_axiom_audit_2026-10-11.json), [independent final review](../../../note/ch13_phase_b_review_2026-10-11.md), [budget/basis/kernel review](../../../note/ch13_budget_basis_kernel_review_2026-10-11.md), [typed-square review](../../../note/ch13_typed_squares_review_2026-10-11.md), [migration plan](../../../note/ch13_promotion_plan_review_2026-10-11.md). The final review discloses authorship and independent checks; proof authors do not certify their own bodies. Flash/Pro tools were unavailable, so exposed inherited Codex agents supplied the recorded sectional and independent-review work.
