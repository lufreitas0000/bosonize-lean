# CH13 Klein factors: Phase A companion

Status: Phase A independently reviewed and frozen at `32b2a03`; Phase B is in progress. 4 theorem proofs are complete and freshly audited; 21 theorem placeholders remain. Four scoped instance omissions have separate independent review. No Phase C/Core promotion is claimed.

Sources: `notes/md/ch13_Klein_factors.md`, `notes/appendices/a05_exponentials_klein_and_vertex_scope.md`, the CH13 TOC entry, applicable restricted-map/tensor-budget/phase corrections in `note/proof_suggestions_revision_2026-10-09.md`, and current frozen CH07, CH11, CH04/A02, CH09 and CH06Ext contracts. Historical brainstorm/API suggestions are advisory; nonexistent `docs/stub_suggestion/` and `docs/proof_suggestion/` were not invented. The A05 exponential and CH14 vertex research sections are excluded from this chapter: this draft asserts no unprojected vertex equality or analytic exponential.

The dedicated drafting agent uses the inherited Codex model because Flash/Pro tools are not exposed. Formalizer and active-focus skills were reread; ACTIVE_FOCUS permits the expressly authorized CH13 scope and does not authorize unrelated Icebox Luther–Emery work. Current workspace state was inspected. Actual API/reducibility and zero-mode failures were journaled before correction in `LOG_DISCOVERY_AND_PIVOTS.md`.

The ordinary product `σ × Band(2*h)` is retained, so these are actual CH07 occupation/budget carriers. `speciesOrder` supplies the lexical total order through the definitionally identical wrapper; four NAMED LOCAL projections (LinearOrder, LT, LE, DecidableEq) are installed explicitly in each module. No global product order instance is exported. This avoids the product componentwise LT or default DecEq silently overriding CAR conventions. The local constants are included in the complete-data axiom audit.

## Actual finite kernel and typed realization

A05 supplies actual joint CAR current words and the actual total-budget partition labels. The complete ambient kernel is

$$
F_{\nu,\mathbf N}^{(K)}v=\sum_{p\in\mathcal P_K}\frac{P(\nu,\mathbf N)}{z_p}\langle u_{\mathbf N,p},v\rangle\,u_{\mathbf N-e_\nu,p}.
$$

Here z(p) is the PRODUCT Hall factor, not its square root. Orthogonal basis coefficient recovery uses 1/z because the squared norm is z. The kernel is not a replacement energy/canonical-map certificate. It is finite actual data on the concrete ambient carrier, including away from the R2 regime; its intended budget identities are proved only with the explicit margins.

The phase is the integer power `(-1)^(Ση<ν(h+Nsη) + (h+Nsν−1))`. The same-species top-removal term occurs once, outside the preceding-species sum. Negative exponents are handled by integer powers, avoiding natural subtraction. `ground_top_annihilation` must derive this exact phase from lexical CH04 preceding occupations. `ground_field_coefficient` retains the whole species twist family and isolates only the GROUND-TO-GROUND coefficient. Deep-hole excited components of the full field are not asserted zero.

The inverse kernel reverses rank-one factors and conjugates the SOURCE phase. It is the ambient adjoint by actual inner-product adjoint algebra. This identity does not make the ambient finite kernel unitary: it kills the complement of the source partition span. Both inverse identities are restricted to the respective physical budgets.

`kleinFromBudget` is complete data from the actual source subtype to the ambient carrier. Codomain membership is a theorem obligation. The eventual fully typed result is `klein_isometry_equiv`: an EXISTS SURJECTIVE linear isometry equivalence between the actual source and target budgets, identified pointwise with this explicit kernel. Stating the bundled realization as a theorem avoids definitions whose data inherit sorryAx from unproved completeness/basis proofs. This design was explicitly approved by the parent before drafting. It neither substitutes an abstract coefficient space for the physical budget nor assumes an isometry certificate.

## Margins and proof plan

- `pairMargin` is per-species R2 for both source Ns and target Ns−eν. It implies both admissibility predicates. The raw kernel basis-action helper uses source R2 only; the inverse basis-action helper uses target R2 only. Ambient kernel range membership needs only target admissibility, and inverse range needs only source admissibility, because each output is a finite sum of the corresponding actual partition states.
- Derive exact partition action by A05 Gram and positive z. Extend inner preservation and inverse identities over the actual complete partition basis. Construct the typed linear maps by codomain restriction only in the proof; prove both inverse equations/surjectivity before bundling `≃ₗᵢ`.
- `kernel_cutoff_consistent` identifies the two operators on the smaller actual budget through common partition labels/actual creator words, under the enlarged J margin. For raising, rho_m adds a creator to species η; the source phase is independent of partitions. Extend this equality from actual partition words to the input budget. For lowering, use the corresponding pull-through recurrence or actual adjoints with explicit source/target budgets. Each typed square existentially supplies both actual Klein isometries and both actual density arrows, identifies all four pointwise with the complete operators, and proves their composition equality.
- Raising/lowering square and intertwining contracts require m>0. The initial m=0 extension was rejected with a concrete reason: same-species rho_0 counts particles and changes by one after charge lowering. Zero transfer is instead handled by the explicit number-shift theorem. No artificial proof step is planned just to consume an unnecessary positivity binder.
- Cross-species anticommutation uses the exact integer parity-product identity under all four actual charge-sector R2 margins. The two final charge functions are equal by explicit `lower_charge_commute`; equality is on ambient vectors with actual source budget membership, so no silent type cast hides an intermediate sector.
- Ground nonzero kernel action uses the actual ground ket and unit phase. `double_kernel_ground_nonzero` proves nonzero double-path action under the full four-sector margin, including ν=η where a doubly lowered sector is controlled. Thus distinct-species anticommutation has actual nonzero paths; additionally, same-species F² need not vanish. For a concrete inhabited distinct-species example take σ=Fin2, h=2, K=0, Ns identically0 and the two distinct indices. No finite Clifford algebra assertion is made.
- The number-shift theorem uses actual charge observables on the source/target subspaces, not invented scalar number operators on an unrelated model.

A05 and CH13 must be proved/reviewed in dependency order. The only anticipated promotion import substitution is `BosonizeStubs.A05MultiSpecies` → `Bosonize.Core.A05MultiSpecies` in CH13, independently reviewed during migration. A05 itself imports the already frozen CH12 dependency chain. Neither phase may mutate old Core.

## Validation and exact interface

The combined target build passed 3398 jobs with exactly 53 expected sorry warnings (A05:28, CH13:25); no errors or non-sorry warnings. Native CH13 error diagnostics completed with partial=false, success=true, empty items and no failed dependencies. Fresh data audit covers all 42 named data/abbreviation/instance constants, INCLUDING the eight local order projections; only standard axioms are permitted and no sorryAx data dependency occurs. See `note/ch13_phase_a_data_axiom_audit_2026-10-11.json` for the source-bound audit. That historical Phase A build establishes data/header elaboration only. Current partial proof evidence is recorded below.

Source SHA-256: `5a9b5da4a02b0d879baa47128089fa3c7a3cc6edab9accb0d846d111cb43fd4e`.

```lean
omit [Fintype σ] in
lemma lower_charge_commute (Ns : σ → ℤ) (ν η : σ) (hne : ν≠η) :
    lowerCharge (lowerCharge Ns ν) η = lowerCharge (lowerCharge Ns η) ν
```

```lean
lemma phase_norm (h : ℕ) (Ns : σ → ℤ) (ν : σ) : ‖kleinPhase h Ns ν‖ = 1
```

```lean
lemma phase_cross_sign (h : ℕ) (Ns : σ → ℤ) (ν η : σ) (hne : ν≠η) :
    kleinPhase h (lowerCharge Ns ν) η * kleinPhase h Ns ν =
      -(kleinPhase h (lowerCharge Ns η) ν * kleinPhase h Ns η)
```

```lean
omit [Fintype σ] [LinearOrder σ] in
lemma r2_admissible (h K : ℕ) (Ns : σ → ℤ) (hR2 : A05.r2 h K Ns) :
    A05.admissible h Ns
```

```lean
lemma ground_top_annihilation (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (ν : σ) (hν : -(h : ℤ)+1 ≤ Ns ν)
    (k : Ch01.Band (2*h)) (hk : k.val=Ns ν) :
    A05.annihilation h ν k (A05.groundKet h Ns) =
      kleinPhase h Ns ν • A05.groundKet h (lowerCharge Ns ν)
```

```lean
lemma ground_field_coefficient (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (ν : σ) (hν : -(h : ℤ)+1 ≤ Ns ν)
    (b : σ → Ch06Ext.BoundaryTwist (2*h)) (x : ℤ) :
    inner ℂ (A05.groundKet h (lowerCharge Ns ν))
      (A05.liftedAnnihilation h b ν x (A05.groundKet h Ns)) =
      (A01.normalization (2*h) : ℂ) * kleinPhase h Ns ν *
        Ch06Ext.liftPhase (2*h) (b ν) x * A01.canonicalRoot (2*h)^(x*Ns ν)
```

```lean
lemma kernel_partition (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hR2 : A05.r2 h K Ns) (p : A05.JointPartitions σ K) :
    kleinKernel h Ns ν K (A05.partitionState h Ns p) =
      kleinPhase h Ns ν • A05.partitionState h (lowerCharge Ns ν) p
```

```lean
lemma inverse_partition (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hR2 : A05.r2 h K (lowerCharge Ns ν)) (p : A05.JointPartitions σ K) :
    inverseKernel h Ns ν K (A05.partitionState h (lowerCharge Ns ν) p) =
      star (kleinPhase h Ns ν) • A05.partitionState h Ns p
```

```lean
lemma kernel_maps_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hN : A05.admissible h (lowerCharge Ns ν)) (v : FockSpace σ h) :
    kleinKernel h Ns ν K v ∈ A05.jointBudget h (lowerCharge Ns ν) K
```

```lean
lemma inverse_maps_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hN : A05.admissible h Ns) (v : FockSpace σ h) :
    inverseKernel h Ns ν K v ∈ A05.jointBudget h Ns K
```

```lean
lemma kernel_inner_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) (v w : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns K) (hw : w ∈ A05.jointBudget h Ns K) :
    inner ℂ (kleinKernel h Ns ν K v) (kleinKernel h Ns ν K w) = inner ℂ v w
```

```lean
lemma inverse_kernel_source (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) (v : FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    inverseKernel h Ns ν K (kleinKernel h Ns ν K v) = v
```

```lean
lemma kernel_inverse_target (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) (v : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h (lowerCharge Ns ν) K) :
    kleinKernel h Ns ν K (inverseKernel h Ns ν K v) = v
```

```lean
lemma kernel_adjoint (h : ℕ) (Ns : σ → ℤ) (ν : σ) (K : ℕ) :
    LinearMap.adjoint (kleinKernel h Ns ν K) = inverseKernel h Ns ν K
```

```lean
theorem klein_isometry_equiv (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) :
    ∃ F : A05.jointBudget h Ns K ≃ₗᵢ[ℂ] A05.jointBudget h (lowerCharge Ns ν) K,
      ∀ v, (F v : FockSpace σ h) = kleinKernel h Ns ν K v
```

```lean
lemma kernel_cutoff_consistent (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K J : ℕ)
    (hKJ : K≤J) (hm : pairMargin h J Ns ν) (v : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns K) :
    kleinKernel h Ns ν J v = kleinKernel h Ns ν K v
```

```lean
lemma kernel_raising_intertwine (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ) (K m : ℕ) (hmpos : 0<m)
    (hm : pairMargin h (K+m) Ns ν) (v : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns K) :
    kleinKernel h Ns ν (K+m) (A05.rho h η (m : ℤ) v) =
      A05.rho h η (m : ℤ) (kleinKernel h Ns ν K v)
```

```lean
lemma kernel_lowering_intertwine (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ) (K m : ℕ) (hmpos : 0<m)
    (hm : pairMargin h (K+m) Ns ν) (v : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns (K+m)) :
    kleinKernel h Ns ν K (A05.rho h η (-(m : ℤ)) v) =
      A05.rho h η (-(m : ℤ)) (kleinKernel h Ns ν (K+m) v)
```

```lean
theorem klein_raising_square (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ) (K m : ℕ) (hmpos : 0<m)
    (hm : pairMargin h (K+m) Ns ν) :
    ∃ F0 : A05.jointBudget h Ns K ≃ₗᵢ[ℂ] A05.jointBudget h (lowerCharge Ns ν) K,
    ∃ F1 : A05.jointBudget h Ns (K+m) ≃ₗᵢ[ℂ] A05.jointBudget h (lowerCharge Ns ν) (K+m),
    ∃ R0 : A05.jointBudget h Ns K →ₗ[ℂ] A05.jointBudget h Ns (K+m),
    ∃ R1 : A05.jointBudget h (lowerCharge Ns ν) K →ₗ[ℂ] A05.jointBudget h (lowerCharge Ns ν) (K+m),
      (∀ v, (F0 v : FockSpace σ h)=kleinKernel h Ns ν K v) ∧
      (∀ v, (F1 v : FockSpace σ h)=kleinKernel h Ns ν (K+m) v) ∧
      (∀ v, (R0 v : FockSpace σ h)=A05.rho h η (m : ℤ) v) ∧
      (∀ v, (R1 v : FockSpace σ h)=A05.rho h η (m : ℤ) v) ∧
      F1.toLinearMap.comp R0 = R1.comp F0.toLinearMap
```

```lean
theorem klein_lowering_square (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ) (K m : ℕ) (hmpos : 0<m)
    (hm : pairMargin h (K+m) Ns ν) :
    ∃ F0 : A05.jointBudget h Ns K ≃ₗᵢ[ℂ] A05.jointBudget h (lowerCharge Ns ν) K,
    ∃ F1 : A05.jointBudget h Ns (K+m) ≃ₗᵢ[ℂ] A05.jointBudget h (lowerCharge Ns ν) (K+m),
    ∃ R0 : A05.jointBudget h Ns (K+m) →ₗ[ℂ] A05.jointBudget h Ns K,
    ∃ R1 : A05.jointBudget h (lowerCharge Ns ν) (K+m) →ₗ[ℂ] A05.jointBudget h (lowerCharge Ns ν) K,
      (∀ v, (F0 v : FockSpace σ h)=kleinKernel h Ns ν K v) ∧
      (∀ v, (F1 v : FockSpace σ h)=kleinKernel h Ns ν (K+m) v) ∧
      (∀ v, (R0 v : FockSpace σ h)=A05.rho h η (-(m : ℤ)) v) ∧
      (∀ v, (R1 v : FockSpace σ h)=A05.rho h η (-(m : ℤ)) v) ∧
      F0.toLinearMap.comp R0 = R1.comp F1.toLinearMap
```

```lean
lemma kernel_cross_anticommute (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ) (hne : ν≠η)
    (K : ℕ) (hm : fourSectorMargin h K Ns ν η) (v : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns K) :
    kleinKernel h (lowerCharge Ns ν) η K (kleinKernel h Ns ν K v) +
      kleinKernel h (lowerCharge Ns η) ν K (kleinKernel h Ns η K v) = 0
```

```lean
lemma kernel_number_shift (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) (v : FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    kleinKernel h Ns ν K (A05.chargeObservable h η v) =
      A05.chargeObservable h η (kleinKernel h Ns ν K v) +
        (if ν=η then (1 : ℂ) else 0) • kleinKernel h Ns ν K v
```

```lean
lemma kernel_ground (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) :
    kleinKernel h Ns ν K (A05.groundKet h Ns) =
      kleinPhase h Ns ν • A05.groundKet h (lowerCharge Ns ν)
```

```lean
lemma kernel_ground_nonzero (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) :
    kleinKernel h Ns ν K (A05.groundKet h Ns) ≠ 0
```

```lean
lemma double_kernel_ground_nonzero (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ)
    (K : ℕ) (hm : fourSectorMargin h K Ns ν η) :
    kleinKernel h (lowerCharge Ns ν) η K
      (kleinKernel h Ns ν K (A05.groundKet h Ns)) ≠ 0
```

## Root exact-source verification

Fresh root inspection independently audits all 42 complete data declarations, including the eight local order projections, with standard axioms only. Native diagnostics on both final source files complete with exactly their 28/25 expected placeholder warnings, zero errors and no failed dependencies. Existing nineteen Core hashes pass against `c3169bf`. Root mathematical review confirms total-energy rather than box budgets, actual lexical CAR, even-hop parity cancellation, genuine product Gram normalization, matching source-conjugate inverse, both typed inverse directions, strict positive-mode squares, the separate number law, and the retained species twist in the physical ground-to-ground coefficient.

An independent finite integer-parity oracle checks 1384 ground top-mode removals and 2176 ordered cross-species phase pairs for h=1,2,3 and one to three species, across admissible negative and positive charges. These finite checks support review and are not Lean proofs or a substitute for the universal phase obligations.

## Reviewed interface freeze

Independent author-distinct review by `/root/ch11_gram_probe`: [PASS](../../../note/ch13_phase_a_review_2026-10-11.md), tied to the final source hash above. All previous manifest records remain identical; only the two reviewed staging entries are added. The committed baseline authorizes proof-body replacements only. All 53 obligations remain unproved at freeze; promotion requires complete proofs, fresh audits and independently reviewed complementary lectures.

## Phase B partial checkpoint — 2026-10-11

Completed and freshly standard-axiom audited: `lower_charge_commute`, `phase_norm`, `phase_cross_sign`, `r2_admissible`. No completed theorem depends on `sorryAx`. The integrated two-module build passes 3398 jobs with exactly 37 warnings for remaining placeholders and no other warnings. Full Phase B and Phase C are pending. See [partial audit](../../../note/ch13_phase_b_partial_audit_2026-10-11.json) and [reviewed instance cleanup](../../../note/ch13_unused_instance_amendment_review_2026-10-11.md). The Phase A source hash above is historical; the current source hash is in the partial audit.
