# CH13 Phase B scoped unused-instance amendment review — 2026-10-11

**PASS** for exactly four scoped instance omissions. Reviewer `/root/ch11_gram_probe`, independent of the proof authors. No repository source or lock edits were made. No other theorem work was undertaken.

The isolated candidate `/tmp/bosonize-ch13/unused-instance-review.lean` (SHA-256 `36dedddeefe14a2af4295e27d66691f960fe8493ddfcd4e02b901f18b77f87a3`) imports the staging chapter, copies the four completed scratch proof bodies under distinct review names, and applies only the requested omissions. `lake env lean -DwarningAsError=true` exited 0. Fresh `#print axioms` for all four candidates contains only permitted standard axioms, with no `sorryAx`. Full evidence is `/tmp/bosonize-ch13/unused-instance-review.log`. Other staging placeholders do not enter these four proof dependencies.

| Original theorem | Scoped amendment | Exact resulting implicit species parameters | Rationale |
| --- | --- | --- | --- |
| `A05.mode_lt_iff` | `omit [Fintype σ] in` | `{σ : Type u} [LinearOrder σ]` | Lexicographic comparison of two pairs does not enumerate species. The actual species order is retained. |
| `A05.joint_normalization_positive` | `omit [LinearOrder σ] in` | `{σ : Type u} [Fintype σ]` | Positivity is a finite product of positive Hall factors; species order plays no role. Finite enumeration remains required. |
| `Ch13.lower_charge_commute` | `omit [Fintype σ] in` | `{σ : Type u} [LinearOrder σ]` | Updates at distinct indices commute by pointwise cases; no species enumeration occurs. The existing order-derived equality decision used by `lowerCharge` remains. |
| `Ch13.r2_admissible` | `omit [Fintype σ] [LinearOrder σ] in` | `{σ : Type u}` | The proof is pointwise integer arithmetic: R2 implies both admissibility inequalities at every species, without enumeration or comparison of species. |

Exact resulting mathematical signatures (namespace qualifiers added for clarity):

```lean
lemma A05.mode_lt_iff {σ : Type u} [LinearOrder σ]
    (h : ℕ) (ν η : σ) (k l : Ch01.Band (2*h)) :
    (ν,k) < (η,l) ↔ ν < η ∨ ν=η ∧ k<l

lemma A05.joint_normalization_positive {σ : Type u} [Fintype σ]
    (K : ℕ) (p : A05.JointPartitions σ K) :
    0 < A05.jointNormalization p

lemma Ch13.lower_charge_commute {σ : Type u} [LinearOrder σ]
    (Ns : σ → ℤ) (ν η : σ) (hne : ν≠η) :
    Ch13.lowerCharge (Ch13.lowerCharge Ns ν) η =
      Ch13.lowerCharge (Ch13.lowerCharge Ns η) ν

lemma Ch13.r2_admissible {σ : Type u}
    (h K : ℕ) (Ns : σ → ℤ) (hR2 : A05.r2 h K Ns) :
    A05.admissible h Ns
```

The first signature uses exactly A05's local lexicographic species order, not a componentwise product comparison. All four conclusions and their explicit hypotheses are preserved. The only changes remove unused implicit instances and consequently broaden availability of the same statements. No carrier, operator, normalization, margin, data definition, or mathematical conclusion changes. Lock amendments should be restricted to the approved changes in the two affected modules; the reviewer does not authorize unrelated interface edits.

## Additional current-source review: 15 integrated proof bodies

**PASS** for the 15 completed bodies present in the current repository snapshot. A05 source SHA-256 `049918d7f25cc0c924bad219206158209d8af3850bb4e281115cbac6dc1159cd`; CH13 source SHA-256 `2b3ebc357970605ff9e2720da0b0c6885c7f747d4fafb79ec842abf893c78b1a`.

This review copied the CURRENT source bodies, preserving the root's corrected `ground_mem_budget` proof through `species_joint_configuration`, and applied the four scoped omissions. The isolated current-source candidate `/tmp/bosonize-ch13/current15-amendment-review.lean`, SHA-256 `2bdd65153960d6f80c8e9ff62a3193a0002814b7d755bedcc59f628cb4bdeb79`, passed fresh warning-as-error compilation, exit0. All 15 fresh axiom reports in `/tmp/bosonize-ch13/current15-amendment-review.log` contain standard axioms only; none contains `sorryAx`. An initial mechanical rename accidentally touched qualified Ch04 references; that failed run was discarded, journaled, corrected, and independently rerun successfully.

Reviewed A05 bodies: `mode_lt_iff`, `species_joint_configuration`, `joint_species_configuration`, `annihilation_car`, `creation_car`, `mixed_car`, `creation_adjoint`, `ground_mem_budget`, `ground_ne_zero`, `joint_normalization_positive`, `charge_budget`. Reviewed CH13 bodies: `lower_charge_commute`, `phase_norm`, `phase_cross_sign`, `r2_admissible`.

The configuration proofs establish both actual finite occupation inverses. CAR/adjoint wrappers invoke frozen actual Ch04 operators with the established lex order. Ground membership proves each actual fiber's charge and zero excitation before using the total species budget. Charge action extends the actual diagonal eigenvalue from supported occupation kets by span induction. Phase-cross-sign computes the charge-update change of the integer exponent and uses the two strict order cases; it includes no sector restrictions or numerical oracle assumptions.

Authorship is unchanged: proof bodies come from the authors' nominated basic/root scratch work and the root's current integrated fixes. This independent reviewer copied and checked those bodies rather than claiming authorship. No unfinished ground-fiber theorem was included; the review does not certify remaining placeholders or complete Phase B.

## Root review of the subsequent tensor ket proof

The root independently inspected the author-distinct `tensor_kets` body. Coordinates reduce the actual tensor to the product of species ket coefficients. In the unequal-configuration case, the proved occupation inverse forces a mismatching species, giving a zero product; in the equal case every coefficient is one. This includes an empty species type without an extra inhabitation assumption. No interface change is introduced. Installed-compiler and fresh integrated axiom evidence is included in the partial audit.
