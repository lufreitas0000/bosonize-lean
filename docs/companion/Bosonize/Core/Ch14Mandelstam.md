# CH14 — Verified finite phases and conditional field comparison

**Status: Phase C complete.** All 24 theorem proofs are complete, warning-free, audited with standard axioms and promoted/frozen in Core. Corresponding lecture updates passed independent preservation and mathematical review. Unconditional field–vertex equality is outside this proved scope.

This companion tracks the exact Lean declarations in `Bosonize/Core/Ch14Mandelstam.lean`. The signatures below were Phase A obligations; their proofs are now complete. The complementary lecture remains [Chapter 14](../../../../notes/md/ch14_Mattis_Mandelstam_formula.md); [A05](../../../../notes/appendices/a05_exponentials_klein_and_vertex_scope.md) supplies the accepted separation of finite candidates and algebraic verification criteria.

The inherited Codex agent is the workflow fallback because the requested Flash/Pro tool tiers are not exposed. Installed Lean elaboration is authoritative; native Lean MCP is available. No existing Core module or lock is edited by this draft.

## Source reconciliation and scope

Adopted: (14.1)–(14.2), their exact plus/minus signs, source zero mode (14.3a), typed ordered composition (14.4), adjoint reversal (14.5), and the common-residual cyclic criterion (14.7). Adapted: actual CAR maps live on the frozen A05 lexicographic occupation Hilbert carrier; projections/restrictions produce genuine source and target subtype maps. Mode sums use zero-based `range M` with positive physical weight `m+1`. The candidate uses a finite Taylor polynomial on each actual compressed budget, and four independent nilpotency obligations justify degree K+1. Generic A05Exp supplies the finite polynomial and filtration criterion.

Rejected: the discarded difference phases, equality inferred from one ground matrix coefficient, unconditional field–vertex equality under numerical margins, omitted projection excursions, and nilpotency inferred merely from finite dimension. No suggestions directories `docs/stub_suggestion` or `docs/proof_suggestion` exist in this checkout; the accepted corrected source notes and immutable Core are the actual inputs.

The exact degree bound requires only positive half-length: total excitation is nonnegative and positive-mode lowering strictly decreases it. No R2 margin is needed for this grading fact. Klein ground reproduction uses the explicit source/target pairMargin; the actual typed candidate itself is defined by projected finite kernels without asserting they are unitary outside completeness margins.

The conditional physical theorem quantifies a source vector v₀, compressed creators G, target maps T and common residual maps. Its physical use must choose the actual `groundVector`, prove the full retained occupation-hole equality, and establish actual cyclicity and equal residuals. These remain physical specialization obligations rather than an unconditional bosonization result. The explicit retained-hole and residual formulas provide concrete input to that work.

## Carriers and complete data

`budgetSet` is exactly CH07's all-species charge predicate and total excitation cutoff. `projection` is the Core orthogonal coordinate projection. `projectedMap` is Ptarget A restricted to the actual source, certified by Core `projection_range`; no theorem stub occurs in its construction. `budgetAdjoint` is the actual finite-dimensional Hilbert adjoint with explicitly reversed source/target carriers. `groundVector` uses proved Core admissibility membership.

`wPlus` and `wMinus` are the actual finite current sums on A05's actual CAR carrier. `compressedPlus` and `compressedMinus` retain PWP, acting as zero outside the budget. `zeroScalar` retains the same species twist as the physical field and the SOURCE integer charge; `zeroMode` is scalar identity on that fixed source budget. `physicalMap` keeps all target losses. `vertexCandidate` composes source Z, actual projected Klein kernel, shifted-input lowering Taylor, actual cutoff transition, and target raising Taylor in this order. Generic `creatorWord` and `cyclicSpan` need no Hilbert assumptions or basis linear independence.

Comments before every definition, local instance and theorem explain the carrier, purpose and physical convention.

## Exact theorem contracts and proof plans

### `cyclic_common_residual`

```lean
theorem cyclic_common_residual (G : I → Module.End R V) (T : I → Module.End R W)
    (A B : V →ₗ[R] W) (residual : I → V →ₗ[R] W) (v₀ : V)
    (hcyclic : cyclicSpan G v₀ = ⊤) (hground : A v₀ = B v₀)
    (hA : ∀ i, A.comp (G i) = (T i).comp A + residual i)
    (hB : ∀ i, B.comp (G i) = (T i).comp B + residual i) : A = B
```

Subtract recurrences; induct over the creator list; put every orbit vector into ker(A−B), extend by Submodule.span_le and hcyclic. Semiring scalars suffice because module addition is a group.

### `projected_map_apply`

```lean
lemma projected_map_apply (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ)
    (A : A05.Operators σ h) (v : A05.jointBudget h Ns Kin) :
    (projectedMap h Ns Nt Kin Kout A v : A05.FockSpace σ h) = projection h Nt Kout (A v)
```

Definitional subtype coercion; rfl.

### `projected_map_adjoint`

```lean
lemma projected_map_adjoint (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ)
    (A : A05.Operators σ h) :
    budgetAdjoint h Ns Nt Kin Kout (projectedMap h Ns Nt Kin Kout A) =
      projectedMap h Nt Ns Kout Kin (LinearMap.adjoint A)
```

Pairing characterization of the actual subtype adjoint; projection self-adjointness and its fixed-point property on members, with source and target reversed.

### `vertex_candidate_adjoint`

```lean
lemma vertex_candidate_adjoint (h M : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kin Kout : ℕ) :
    let Nt := Ch13.lowerCharge Ns ν
    budgetAdjoint h Ns Nt Kin Kout (vertexCandidate h M b Ns ν x Kin Kout) =
      (A01.normalization (2*h) : ℂ) •
        (budgetAdjoint h Ns Ns Kin Kin (zeroMode h b Ns ν x Kin)).comp
          ((budgetAdjoint h Ns Nt Kin Kin (projectedMap h Ns Nt Kin Kin (Ch13.kleinKernel h Ns ν Kin))).comp
            ((budgetAdjoint h Nt Nt Kin Kin (A05Exp.finiteTaylor Kin (projectedMap h Nt Nt Kin Kin (wPlus h M ν x)))).comp
              ((budgetAdjoint h Nt Nt Kin Kout (projectedMap h Nt Nt Kin Kout LinearMap.id)).comp
                (budgetAdjoint h Nt Nt Kout Kout (A05Exp.finiteTaylor Kout (projectedMap h Nt Nt Kout Kout (wMinus h M ν x)))))))
```

Expand the five typed factors, use adjoint_comp in reverse order and the real normalization conjugation. Do not commute factors.

### `w_plus_periodic`

```lean
lemma w_plus_periodic (h M : ℕ) [NeZero (2*h)] (ν : σ) (x w : ℤ) :
    wPlus h M ν (x+w*(2*h : ℕ)) = wPlus h M ν x
```

A01.character_representative_independent for each positive integer mode, then finite-sum congruence.

### `w_minus_periodic`

```lean
lemma w_minus_periodic (h M : ℕ) [NeZero (2*h)] (ν : σ) (x w : ℤ) :
    wMinus h M ν (x+w*(2*h : ℕ)) = wMinus h M ν x
```

The same character law with negative momentum, preserving the exterior minus sign.

### `w_plus_adjoint`

```lean
lemma w_plus_adjoint (h M : ℕ) [NeZero (2*h)] (ν : σ) (x : ℤ) :
    LinearMap.adjoint (wPlus h M ν x) = -wMinus h M ν x
```

Adjoint of finite sum/scalar, A05.rho_adjoint, A01.complex_character_conj; rational denominator is real.

### `w_minus_adjoint`

```lean
lemma w_minus_adjoint (h M : ℕ) [NeZero (2*h)] (ν : σ) (x : ℤ) :
    LinearMap.adjoint (wMinus h M ν x) = -wPlus h M ν x
```

Same operations with the exterior minus; recover the reciprocal sign.

### `compressed_plus_nilpotent`

```lean
lemma compressed_plus_nilpotent (h M : ℕ) (hh : 0<h) (Ns : σ → ℤ) (K : ℕ) (ν : σ) (x : ℤ) :
    compressedPlus h M Ns K ν x ^ (K+1) = 0
```

Actual A05.rho_budget_map and rho_lowering_budget_zero make each positive mode strictly lower total excitation. Combine projection range and nonnegative excitation in A05Exp.filtration_nilpotent. No finite-dimensionality argument.

### `compressed_minus_nilpotent`

```lean
lemma compressed_minus_nilpotent (h M : ℕ) (hh : 0<h) (Ns : σ → ℤ) (K : ℕ) (ν : σ) (x : ℤ) :
    compressedMinus h M Ns K ν x ^ (K+1) = 0
```

Actual P self-adjoint and W⁺†=−W⁻ give raising compression as minus lowering adjoint. Transfer power-zero under adjoint.

### `projected_plus_nilpotent`

```lean
lemma projected_plus_nilpotent (h M : ℕ) (hh : 0<h) (Ns : σ → ℤ) (K : ℕ) (ν : σ) (x : ℤ) :
    projectedMap h Ns Ns K K (wPlus h M ν x) ^ (K+1) = 0
```

Subtype coercion commutes with powers of the compression, using P fixed on actual source vectors; transfer ambient power zero.

### `projected_minus_nilpotent`

```lean
lemma projected_minus_nilpotent (h M : ℕ) (hh : 0<h) (Ns : σ → ℤ) (K : ℕ) (ν : σ) (x : ℤ) :
    projectedMap h Ns Ns K K (wMinus h M ν x) ^ (K+1) = 0
```

The identical subtype/ambient argument for compressed raising.

### `zero_scalar_norm`

```lean
omit [Fintype σ] [LinearOrder σ] in
lemma zero_scalar_norm (h : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) : ‖zeroScalar h b Ns ν x‖ = 1
```

Product of Core lift_phase_norm and canonical-root character norm.

### `zero_scalar_winding`

```lean
omit [Fintype σ] [LinearOrder σ] in
lemma zero_scalar_winding (h : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x w : ℤ) :
    zeroScalar h b Ns ν (x+w*(2*h : ℕ)) = Ch06Ext.holonomy (2*h) (b ν)^w * zeroScalar h b Ns ν x
```

Core lift_phase_winding and integer-charge character representative independence.

### `zero_mode_winding`

```lean
lemma zero_mode_winding (h : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x w : ℤ) (K : ℕ) :
    zeroMode h b Ns ν (x+w*(2*h : ℕ)) K =
      Ch06Ext.holonomy (2*h) (b ν)^w • zeroMode h b Ns ν x K
```

Scalar identity map and zero_scalar_winding; no sector shift.

### `zero_mode_adjoint`

```lean
lemma zero_mode_adjoint (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (K : ℕ) :
    LinearMap.adjoint (𝕜 := ℂ) (E := A05.jointBudget h Ns K) (F := A05.jointBudget h Ns K) (zeroMode h b Ns ν x K) = star (zeroScalar h b Ns ν x) • LinearMap.id
```

Actual subtype adjoint conjugates scalar and fixes identity. No nonzero-length assumption is needed for this algebraic property.

### `zero_mode_unitary`

```lean
lemma zero_mode_unitary (h : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (K : ℕ) :
    LinearMap.adjoint (𝕜 := ℂ) (E := A05.jointBudget h Ns K) (F := A05.jointBudget h Ns K) (zeroMode h b Ns ν x K) * zeroMode h b Ns ν x K = 1 ∧
      zeroMode h b Ns ν x K * LinearMap.adjoint (𝕜 := ℂ) (E := A05.jointBudget h Ns K) (F := A05.jointBudget h Ns K) (zeroMode h b Ns ν x K) = 1
```

zero_scalar_norm yields conjugate-times-scalar=1 in both orders.

### `klein_zero_ground`

```lean
lemma klein_zero_ground (h : ℕ) (hh : 0<h) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (K : ℕ) (hm : Ch13.pairMargin h K Ns ν) :
    Ch13.kleinKernel h Ns ν K (zeroScalar h b Ns ν x • A05.groundKet h Ns) =
      (zeroScalar h b Ns ν x * Ch13.kleinPhase h Ns ν) • A05.groundKet h (Ch13.lowerCharge Ns ν)
```

Linear map scalar action plus Ch13.kernel_ground; source phase retained before charge lowering.

### `physical_occupation_expansion`

```lean
lemma physical_occupation_expansion (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kout : ℕ) (S : A05.Occupation σ h) :
    projection h (Ch13.lowerCharge Ns ν) Kout (A05.liftedAnnihilation h b ν x (A02.ket S)) =
      (A01.normalization (2*h) : ℂ) •
        ∑ k : Ch01.Band (2*h), if (ν,k) ∈ S then
          (Ch06Ext.twistedCharacter (2*h) (b ν) k x * Ch04.fermionSign (ν,k) S) •
            projection h (Ch13.lowerCharge Ns ν) Kout (A02.ket (S.erase (ν,k))) else 0
```

Expand actual A05 Fourier field, apply Ch04.annihilation_ket and distribute the target projection; retain every hole and sign.

### `physical_ground_expansion`

```lean
lemma physical_ground_expansion (h : ℕ) (hh : 0<h) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (hN : A05.admissible h Ns) (ν : σ) (x : ℤ) (Kin Kout : ℕ) :
    (physicalMap h b Ns ν x Kin Kout (groundVector h hh Ns hN Kin) : A05.FockSpace σ h) =
      (A01.normalization (2*h) : ℂ) •
        ∑ k : Ch01.Band (2*h), if (ν,k) ∈ A05.groundConfiguration h Ns then
          (Ch06Ext.twistedCharacter (2*h) (b ν) k x * Ch04.fermionSign (ν,k) (A05.groundConfiguration h Ns)) •
            projection h (Ch13.lowerCharge Ns ν) Kout
              (A02.ket ((A05.groundConfiguration h Ns).erase (ν,k))) else 0
```

Specialize physical_occupation_expansion to the exact source ground and projected_map_apply. Source membership comes from Core.

### `projected_recurrence_residual`

```lean
lemma projected_recurrence_residual (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ)
    (c rho : A05.Operators σ h) :
    let Pin := projection h Ns Kin
    let Pout := projection h Nt Kout
    (Pout*c*Pin)*(Pin*rho*Pin) - (Pout*rho*Pout)*(Pout*c*Pin) =
      Pout*(c*rho-rho*c)*Pin - Pout*c*(1-Pin)*rho*Pin + Pout*rho*(1-Pout)*c*Pin
```

Expand the exact identity by noncomm_ring, using P²=P to identify the compressed terms. Neither boundary excursion is discarded.

### `physical_map_winding`

```lean
lemma physical_map_winding (h : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x w : ℤ) (Kin Kout : ℕ) :
    physicalMap h b Ns ν (x+w*(2*h : ℕ)) Kin Kout =
      Ch06Ext.holonomy (2*h) (b ν)^w • physicalMap h b Ns ν x Kin Kout
```

Finite Fourier character winding, then linearity of target projection/restriction.

### `vertex_candidate_winding`

```lean
lemma vertex_candidate_winding (h M : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x w : ℤ) (Kin Kout : ℕ) :
    vertexCandidate h M b Ns ν (x+w*(2*h : ℕ)) Kin Kout =
      Ch06Ext.holonomy (2*h) (b ν)^w • vertexCandidate h M b Ns ν x Kin Kout
```

W phases are periodic; zero_mode_winding supplies the only external factor, and all other typed factors are linear.

### `field_vertex_of_common_residual`

```lean
theorem field_vertex_of_common_residual (h M : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kin Kout : ℕ)
    {I : Type*} (G : I → Module.End ℂ (A05.jointBudget h Ns Kin))
    (T : I → Module.End ℂ (A05.jointBudget h (Ch13.lowerCharge Ns ν) Kout))
    (residual : I → A05.jointBudget h Ns Kin →ₗ[ℂ] A05.jointBudget h (Ch13.lowerCharge Ns ν) Kout)
    (v₀ : A05.jointBudget h Ns Kin)
    (hcyclic : cyclicSpan G v₀ = ⊤)
    (hground : physicalMap h b Ns ν x Kin Kout v₀ = vertexCandidate h M b Ns ν x Kin Kout v₀)
    (hA : ∀ i, (physicalMap h b Ns ν x Kin Kout).comp (G i) =
      (T i).comp (physicalMap h b Ns ν x Kin Kout) + residual i)
    (hB : ∀ i, (vertexCandidate h M b Ns ν x Kin Kout).comp (G i) =
      (T i).comp (vertexCandidate h M b Ns ν x Kin Kout) + residual i) :
    physicalMap h b Ns ν x Kin Kout = vertexCandidate h M b Ns ν x Kin Kout
```

Apply cyclic_common_residual to the actual two typed maps. Full ground-vector equality, cyclic span and both common residual recurrences remain explicit hypotheses.

## Validation boundary

The source is a Phase A candidate until independent review and a scoped lock. A successful placeholder build confirms type elaboration only. Before freezing, record the exact source SHA, declaration counts, data-only standard-axiom audit, native diagnostic results and independent review. After proofs, require zero warnings/placeholders, all theorem dependencies standard-axiom audited, unchanged old Core hashes, and independently reviewed lecture synchronization before promotion.

Phase A author validation (2026-10-12): source SHA-256 `6e11f90d2801fc18b0e51fe5bde2f19d137590199943824d950039ee347c5c16`; 24 one-sorry theorem obligations and 19 complete data/instance declarations. `lake build BosonizeStubs.Ch14Mandelstam` succeeded (3405 jobs), with precisely the 24 expected placeholder warnings and no errors or other warnings. A fresh audit of all 19 data declarations uses only `propext`, `Classical.choice`, `Quot.sound`, and no `sorryAx`: [audit](../../../../note/ch14_phase_a_data_axiom_audit_2026-10-12.json). Native Lean MCP diagnostics independently completed with exactly 24 sorry warnings, no errors, no timeout/partial result and no failed dependencies. Independent reviewer decision is still required before freezing.

## Reviewed Phase B instance cleanup

Exactly zero_scalar_norm and zero_scalar_winding omit unused finite enumeration and species-order instances. Their external twist, nonzero length and explicit parameters remain. Independent compiler/signature review: note/ch14_phase_b_instance_cleanup_review_2026-10-12.md. All other interfaces and data are unchanged.

## Complete Phase B — 2026-10-12

All 37 combined theorem proofs and 20 data declarations are complete and freshly audited with only standard axioms; no placeholders or warnings remain. Both native diagnostic calls complete with empty items. The combined build passes 3405 jobs; strict guard verifies 793 statements and 632 commands. Independent final review records authorship and the root’s distinct review of the reviewer-authored eight proofs. Only the two previously reviewed scalar-instance omissions changed the frozen interface. Exact current source hashes and all 57 axiom reports are in note/ch14_phase_b_independent_audit_2026-10-12.json. Phase C promotion and complementary lecture review are next. Earlier Phase A status and placeholder counts are historical.

## Verified Core completion and synchronization — 2026-10-13

The final source SHA-256 is `0d3feed562023e5d8a20027021014cc56512d636b58848fa7a8122b61cc320fc`. Phase B completed at `339b4c0`; source migration follows the independently reviewed import-only plan. Existing 21 Core modules are unchanged. All 37 combined proofs and 20 data declarations are audited again through the Core aggregator. Full CI and synchronization evidence are recorded in [validation](../../../../note/ch14_phase_c_validation_2026-10-13.md). The [independent lecture review](../../../../note/ch14_phase_c_pedagogical_review_2026-10-12.md) binds the unchanged CH14 and A05 note/source hashes and confirms preservation of the original reference exposition.

The [CH14 lecture](../../../../notes/md/ch14_Mattis_Mandelstam_formula.md) explains actual phase nilpotency, typed projection losses, adjoint reversal, explicit holonomy and the full-vector/common-residual cyclic criterion. The [A05 lecture](../../../../notes/appendices/a05_exponentials_klein_and_vertex_scope.md) explains generic exact finite exponentials while preserving separate research proposals. Historical draft build counts above are superseded by the fresh completion evidence.
