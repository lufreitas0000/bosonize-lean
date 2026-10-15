## Verdict: FAIL (1 blocking issue: two theorems are false as stated; there is a one-line fix)

The draft follows the guidance faithfully. I re-derived every key computation by hand and all of them check out. The exception is the diagonal pair: `density_kernel_diagonal` and `density_kernel_diagonal_pos` are **false at ζ = 0** because they lack `hζ`. The guidance (D4 item 10) left out the same hypothesis, so the error was inherited from there. If you add `(hζ : ζ ≠ 0)` to both, I would vote PASS. The non-blocking items below are worth applying before the freeze, because they change interface shape.

## Coverage table
| claim | declaration(s) | status |
|---|---|---|
| c01 | none; cited Core `Ch02.finite_dimensional_no_go`, `Ch08.finite_ccr_obstruction` | justified (cite only, per guidance) |
| c02 | oscPairing_monomial, oscPairing_conj, oscPairing_self_nonneg, oscPairing_self_eq_zero, oscCreation_pairing_adjoint, osc_ccr, osc_annihilators_commute, osc_creators_commute, oscAnnihilation_one | covered |
| c03 | omega0_eq_pairing, omega0_one, omega0_gramSum, omega0_ccr_descends | covered, but partial: only the [A,C] relation (N1) |
| c04 | bogoliubovMap_inverse, bogoliubovMap_inverse_rev | "if" direction only; converse optional (N4) |
| c05 | omegaP_one, omegaP_gramSum, omegaP_ccr_descends, omegaP_mul_dressed_annihilator, omegaP_dressed_creator_mul, bogoliubovMap_word_adjoint | covered |
| c06 | omegaP_commutator | covered |
| c07 | omegaP_creator_annihilator_right, omegaP_annihilator_creator_right | covered, right branch only (N2) |
| c08 | omegaP_creator_creator_right, omegaP_annihilator_annihilator_right | covered |
| c09 | omegaP_cross_creator_creator, omegaP_cross_annihilator_annihilator, omegaP_cross_creator_annihilator | covered (A_R C_L missing, N2) |
| c10 | s_sq_eq_luttinger, c_sq_eq_luttinger | covered |
| c11 | oscDensityR, fockDensityR (defs) | covered |
| c12 | ordered_density_kernel, ordered_density_kernel_lattice | covered |
| c13 | symmetrized_density_kernel | covered |
| c14 | density_commutator_expectation | covered |
| c15 | density_kernel_diagonal, density_kernel_diagonal_pos | **FALSE as stated (B1)** |
| c16 | ordered_density_free | covered |
| c17 | vectorState_ground_one, vectorState_adjoint_mul_self | covered |
| c18 | ground_lowering_raising, ground_raising_lowering, ground_raising_raising, ground_lowering_lowering | covered |
| c19 | fock_ground_density_kernel, fock_ground_matches_free_state (docstring correct) | covered |
| c20 | excited_ket_norm_sq, ground_dressed_number, ground_dressed_reverse, ground_not_dressed_vacuum | covered |
| c21 | compressed_gram, compressed_common_kernel_trivial, compressed_no_vacuum_density, compressed_kernel_of_s_zero, note_compressed_witness | covered |
| c22, c23, c24 | none | justified deferral |
| c25 | concrete_correlation_witness | covered; all numbers re-verified |

## Independent verifications (by hand, against the Core sources)
- **Conventions.** Ch18 `HyperbolicPair = ⟨c, s, c²−s²=1⟩` with no sign constraint. `luttingerG = (c−s)²` and `luttingerGInv = (c+s)²`.
  - A07 `bogoliubovCreator = c ρ_{m,η} + s ρ_{−m,η̄}` and `bogoliubovAnnihilator = c ρ_{−m,η} + s ρ_{m,η̄}`. These match β_{c,s}(C_ν)=cC_ν+sA_ν̄ and β_{c,s}(A_ν)=cA_ν+sC_ν̄ in `bogoliubovMap`.
  - `A05.rho` uses `validPairs` (unwrapped transfers), so ρ_{−m} really lowers (`rho_lowering_budget_zero`).
  - The Core `chiralField` uses ζ^{−mx}ρ_m and ζ^{mx}ρ_{−m}, the same orientation as `oscDensityR`/`fockDensityR` and N19 (19.4).
- **β inverse.** β_{c,s}(c g − s ḡ) = (c²−s²) g, because `oppositeOrientation` and `!` are involutions. True for any real c, s with c²−s²=1.
- **Contractions with ω_P = ω₀∘β_{c,−s}:**
  - C_R^i A_R^j → (cC_R − sA_L)(cA_R − sC_L). Only the term s² A_L^i C_L^j survives, giving δ m s².
  - A_R C_R → c² A_R C_R, giving δ m c².
  - C_R C_R and A_R A_R give 0.
  - C_R^i C_L^j: only −cs A_L^i C_L^j survives, giving −δ m c s.
  - A_R^i A_L^j: only −cs A_R^i C_R^j survives, giving −δ m c s.
  - C_R A_L gives 0. A_R C_L gives 0 too, but it is not stated.
  - With ω₀∘β_{c,s} the cross terms would come out +mcs, so the direction is correct.
- **Annihilation laws.** ω_P(a β_{c,s}(A)) = ω₀(β'(a)·A) = coeff₀(π(β'a)·0) = 0, and ω_P(β(C)a) = coeff₀(X_p·…) = 0. Both need `hp.hyperbolic_id`, which is available.
- **omegaP_ccr_descends.** π(β'([A_p,C_q] − δw)) = (c²−s²)δw − δw = 0, using w_{p̄} = w_p. True.
- **omegaP_commutator.** mc² − ms² = m, with no (c,s) dependence. True.
- **Word adjoint.** π(g)^† = π(g*) by `oscCreation_pairing_adjoint` plus `oscPairing_conj`. Also β(g)^† = c g* + s (ḡ)* = β(g*) for real c, s. So π(β w)^† = π(β(wordDagger w)). The stated shape ⟨x, π(β w†) y⟩ = ⟨π(β w) x, y⟩ is correct and needs no `hcs`.
- **Positivity.** gramSum = ⟨v,v⟩ with v = Σ z_j π(β' w_j)1. Complex z with `star` is correct, and stronger than the "real coefficients" in flag 7. `oscPairing 1 q = coeff₀ q` because N_0 = 1, so `omega0_eq_pairing` holds.
- **Ordered kernel.** D = L⁻² Σ_i m_i [s² ζ^{−m x}ζ^{m y} + c² ζ^{m x}ζ^{−m y}]. Combining the factors needs ζ ≠ 0, which is assumed. This equals `densityKernel h M ζ c² s² d` with d = x.val − y.val, the (2h)⁻² prefactor and the argument order (c2, s2) all correct.
  - The lattice version holds under `IsPrimitiveRoot ζ (2h)`.
  - Commutator: (c²−s²)(ζ^{md} − ζ^{−md}) = `densityKernel 1 (−1)`.
  - Symmetrized: (c²+s²)/2 = (g+g⁻¹)/4 by `hyperbolic_coeff_eq_luttinger`.
  - s² = (g+g⁻¹−2)/4 and c² = (g+g⁻¹+2)/4 are true, since g + g⁻¹ = 2c² + 2s².
- **Fock side.**
  - ⟨Ω,ρ_{−m}ρ_nΩ⟩ = Schwinger(−m,n) = δ m, needing m+n+|Ns r| ≤ h, which follows from marginAt h M 0.
  - The other three Fock contractions vanish via ρ_{−k}Ω = 0 and the adjoint.
  - The Fock kernel is L⁻² Σ m ζ^{md} = `densityKernel 1 0`.
  - Dressed contractions: ‖ÃΩ‖² = s²‖excitedKet η̄‖² = s² m (needs branchMargins), and the reverse order is m + ms² = mc².
- **Witness numbers** (concretePair = (5/4, 3/4) via `ofParams`, m = 2):
  - Abstract: 2·9/16 = 9/8; 2·25/16 = 25/8; −2·15/16 = −15/8.
  - D(0,0) = (34/16)·3/256 = 51/2048.
  - Fock: branchMargins 8 2 0 holds (4 ≤ 8); ⟨ρ_{−2}ρ_2⟩ = 2; dressed value 9/8; ρ(0)ρ(0) = 3/256.
  - `admissible 8 0` holds (Ch07: −h ≤ N ≤ h).
- **Compressed matrices** (basis 1, X_R, X_L at w=1):
  - Ã_R = cA_R + sC_L, i.e. entries (0,1)=c and (2,0)=s, which matches QR.
  - Ã_L = cA_L + sC_R, i.e. entries (0,2)=c and (1,0)=s, which matches QL.
  - The Gram matrices are diag(s², c², 0) + diag(s², 0, c²) = diag(2s², c², c²).
  - Kernel: c ≠ 0 since c² ≥ 1, and s ≠ 0, so v = 0. Every column of ρ lies in the kernel, so ρ = 0 and trace ≠ 1.
  - At s = 0, e₀ lies in the kernel.
  - (5/3, 4/3) gives (32/9, 25/9, 25/9).

## Per-theorem review (name | back-translation | F1 | F2 | notes)
| name | math | F1 | F2 | notes |
|---|---|---|---|---|
| oscPairing_monomial | ⟨X^r,X^s⟩=δ N_r | ok | ok | |
| oscPairing_conj | conj⟨p,q⟩=⟨q,p⟩ | ok | ok | |
| oscPairing_self_nonneg | Re⟨p,p⟩≥0 | ok | ok | |
| oscPairing_self_eq_zero | ⟨p,p⟩=0⇔p=0 | ok | ok | needs N_r>0, which holds (w≥1) |
| oscCreation_pairing_adjoint | ⟨X_p x,y⟩=⟨x,w∂_p y⟩ | ok | ok | |
| osc_ccr | [A_p,C_q]=δ w_p | ok | ok | sign matches Fock [ρ_{−m},ρ_m]=m |
| osc_annihilators_commute / osc_creators_commute | [A,A]=[C,C]=0 | ok | ok | |
| oscAnnihilation_one | A·1=0 | ok | ok | |
| omega0_eq_pairing | ω₀(a)=⟨1,π(a)1⟩ | ok | ok | |
| omega0_one | ω₀(1)=1 | ok | ok | |
| omega0_gramSum | Σ z̄_i z_j ω₀(w_i†w_j) ≥ 0, real | ok | ok | |
| omega0_ccr_descends | ω₀(a([A_p,C_q]−δw)b)=0 | ok | ok | partial ideal, N1 |
| bogoliubovMap_inverse(_rev) | β_{c,s}β_{c,−s}=id, both orders | ok | ok | |
| bogoliubovMap_word_adjoint | π(β w)^†=π(β w†) | ok | ok | true for all real c, s |
| omegaP_one / omegaP_gramSum / omegaP_ccr_descends | normalization, positivity, CCR | ok | ok | |
| omegaP_mul_dressed_annihilator | ω_P(a·Ã)=0 | ok | ok | direction verified |
| omegaP_dressed_creator_mul | ω_P(C̃·a)=0 | ok | ok | |
| omegaP_commutator | ω_P(AC)−ω_P(CA)=m | ok | ok | non-multiplicativity witness |
| vectorState_ground_one | ⟨Ω,Ω⟩=1 | ok | ok | |
| vectorState_adjoint_mul_self | ⟨ψ,X†Xψ⟩=‖Xψ‖² | ok | ok | |
| compressed_gram | QRᴴQR+QLᴴQL=diag(2s²,c²,c²) | ok | ok | for all real c, s |
| compressed_common_kernel_trivial | s≠0 ⇒ ker∩ker=0 | ok | ok | |
| compressed_no_vacuum_density | no trace-1 ρ with QRρ=QLρ=0 | ok | ok | ρ not required PSD, so stronger |
| compressed_kernel_of_s_zero | s=0 ⇒ e₀ in the kernel | ok | ok | shows hs is necessary |
| note_compressed_witness | diag(32/9,25/9,25/9) | ok | ok | |
| omegaP_creator_annihilator_right | δ m s² | ok | ok | |
| omegaP_annihilator_creator_right | δ m c² | ok | ok | |
| omegaP_creator_creator_right / omegaP_annihilator_annihilator_right | 0 | ok | ok | |
| omegaP_cross_creator_creator / omegaP_cross_annihilator_annihilator | −δ m c s | ok | ok | direction detector |
| omegaP_cross_creator_annihilator | ω(C_R A_L)=0 | ok | ok | |
| ordered_density_kernel | D = L⁻²Σ m(s²ζ^{−md}+c²ζ^{md}) | ok | ok | NeZero unused (N3) |
| ordered_density_kernel_lattice | same, with (x−y) characters | ok | ok | |
| density_commutator_expectation | D(x,y)−D(y,x) = (1,−1) kernel | ok | ok | |
| symmetrized_density_kernel | (g+g⁻¹)/4 on both characters | ok | ok | |
| s_sq_eq_luttinger / c_sq_eq_luttinger | s²,c² via g | ok | ok | |
| **density_kernel_diagonal** | D(x,x)=(c²+s²)M(M+1)/(2L²) | **FALSE at ζ=0** | — | B1 |
| **density_kernel_diagonal_pos** | Re D(x,x)>0 | **FALSE at ζ=0** | — | B1 |
| ordered_density_free | s=0 ⇒ free kernel | ok | ok | |
| ground_lowering_raising | ⟨ρ_{−m}ρ_n⟩=δ m | ok | ok | hh is redundant |
| ground_raising_lowering / ground_raising_raising / ground_lowering_lowering | 0 | ok | ok | |
| excited_ket_norm_sq | ‖ρ_mΩ‖²=m | ok | ok | |
| ground_dressed_number | ⟨Ω,C̃ÃΩ⟩=ms² | ok | ok | |
| ground_dressed_reverse | ⟨Ω,ÃC̃Ω⟩=mc² | ok | ok | |
| ground_not_dressed_vacuum | ≠0 when s≠0 | ok | ok | |
| fock_ground_density_kernel | Fock ⟨ρρ⟩ = free kernel | ok | ok | |
| fock_ground_matches_free_state | equals D at freePair | ok | ok | docstring correctly disclaims state identification |
| concrete_correlation_witness | 9/8, 25/8, −15/8, 51/2048, margins, 2, 9/8, ≠0, 3/256 | ok | ok | every s≠0; uses x=0, so ζ-safe |

**Data definitions:** all correct as written. This covers oscPairing (sum over p.support equals the full sum; conjugate-linear in the first slot), oscMonomialNorm, oscRep, omega0, bogoliubovMap, omegaP, wordDagger (reverse plus bit flip only), gramSum, vectorState, compressedQR/QL, densityKernel, oscDensityR, fockDensityR, freePair and noteCompressedPair.
- Hypotheses are minimal except for the redundant `[NeZero (2*h)]` and `hh`, which are harmless and satisfiable.
- `IsPrimitiveRoot` is used exactly where needed.
- The marginAt / branchMargins choices are exactly right: right species only for the contraction lemmas, both branches for the dressed ones.

## Blocking issues
**B1. `density_kernel_diagonal` and `density_kernel_diagonal_pos` are false (F1/provability).**
- **Why:** `integerCharacter` is a zpow. With ζ = 0 and x.val ≠ 0, each character 0^{±m·x.val} is 0, so ρ_R(x) = 0 and D(x,x) = 0.
- **Counterexample:** h=1, M=1, ζ=0, hp=freePair, x=(1 : ZMod 2). The LHS is 0. The RHS is 1·1/4 = 1/4, and `0 < 0` is false.
- **Fix:** add `(hζ : ζ ≠ 0)`:
```lean
theorem density_kernel_diagonal (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x : ZMod (2 * h)) :
    orderedDensityCorrelation h M ζ hp x x =
      ((((hp.c ^ 2 + hp.s ^ 2) * ((M * (M + 1) : ℝ) / 2) / ((2 * h : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)) := by sorry

theorem density_kernel_diagonal_pos (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x : ZMod (2 * h))
    (hh : 0 < h) (hM : 1 ≤ M) :
    0 < (orderedDensityCorrelation h M ζ hp x x).re := by sorry
```
- **Also:** patch guidance D4 item 10 the same way. The witness is unaffected, because it uses x=0 and canonicalRoot ≠ 0.

## Non-blocking issues
**N1. `omega0_ccr_descends` / `omegaP_ccr_descends` cover only the [A,C] relation.** "Descends through the CCR ideal" (c03) also needs [A,A] and [C,C]. CH20b quotient and Wick arguments will want these. Add:
```lean
theorem omega0_ccr_descends_aa (M : ℕ) (a b : OscAlgebra M) (p q : OscMode M) :
    omega0 M (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (false, q) -
      FreeAlgebra.ι ℂ (false, q) * FreeAlgebra.ι ℂ (false, p)) * b) = 0 := by sorry
theorem omega0_ccr_descends_cc (M : ℕ) (a b : OscAlgebra M) (p q : OscMode M) :
    omega0 M (a * (FreeAlgebra.ι ℂ (true, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (true, p)) * b) = 0 := by sorry
```
Add the matching `omegaP_ccr_descends_aa` and `omegaP_ccr_descends_cc` with `hp`. Both are true: β' maps [A,A] to (c²·0 − cs·0 − cs·0 + s²·0) under π.

**N2. Contractions are stated only for ν = right, and A_R C_L is missing.** CH20b's φ/θ combinations need the left branch and the full cross table. Since freezing is irreversible, generalize now (all verified true):
```lean
theorem omegaP_creator_annihilator (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (ν : Bosonize.A06.Orientation) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.creatorGen M ν i * Bosonize.A08.annihilatorGen M ν j) =
      if i = j then ((i.val + 1 : ℕ) : ℂ) * (hp.s : ℂ) ^ 2 else 0 := by sorry
-- likewise omegaP_annihilator_creator (c²), omegaP_creator_creator (0), omegaP_annihilator_annihilator (0) for general ν;
-- cross with η := Bosonize.A07Interactions.oppositeOrientation ν:
--   C_ν C_η and A_ν A_η = if i = j then -(m c s) else 0
--   C_ν A_η = 0 and A_ν C_η = 0
```
You can keep the `_right` names as corollaries or drop them.

**N3. Some hypotheses are unused.**
- `[NeZero (2*h)]` is unused in ordered_density_kernel, density_commutator_expectation, symmetrized_density_kernel, ordered_density_free and the diagonal theorems. At h=0 both sides are 0.
- `hh : 0 < h` is implied by marginAt in the ground_* theorems.
- These are harmless: satisfiable, not vacuity-inducing. Optional cleanup.

**N4. The converse of c04 ("iff") is not stated.** This is optional:
```lean
theorem bogoliubovMap_inverse_iff (M : ℕ) [NeZero M] (c s : ℝ) :
    (bogoliubovMap M c s).comp (bogoliubovMap M c (-s)) = AlgHom.id ℂ (OscAlgebra M) ↔ c ^ 2 - s ^ 2 = 1 := by sorry
```
It is true: the composite sends g to (c²−s²)g, and `FreeAlgebra.ι` of a generator is nonzero.

**N5. Downstream CH20b.**
- The naming is sensible: `A08OscillatorStates` leaves room for `A08ChargeVertices`. `omegaP`, `bogoliubovMap`, `creatorGen`/`annihilatorGen` and `oscDensityR` are reusable.
- A08 has no series carrier, no multi-point Wick moments and no charge sector. CH20b must define these: a coefficientwise extension `PowerSeries.mk (fun n => omegaP M hp (PowerSeries.coeff _ n X))` (omegaP is linear, not a ring hom, so `PowerSeries.map` does not apply), plus a Wick/Gaussian lemma.
- With N1 and N2 applied, the two-point table CH20b needs would be complete.
- Optionally add an orientation-parametrized `oscDensity (ν)` using `A06.orientationSign`, mirroring Core `chiralField`. The left branch is listed as optional in the guidance.

**N6. Minor documentation points.** Flag 7 says "real coefficients", but gramSum uses complex z with star; that is correct and stronger. `compressed_no_vacuum_density` does not require ρ to be PSD, which is also stronger. Neither needs action.

## Machine summary
```json
{"verdict": "FAIL", "blocking": [{"id": "B1", "decl": "Bosonize.Ch19.density_kernel_diagonal, Bosonize.Ch19.density_kernel_diagonal_pos", "kind": "F1", "fix": "Add hypothesis (hζ : ζ ≠ 0) after (ζ : ℂ) in both theorems; counterexample h=1,M=1,ζ=0,hp=freePair,x=1 gives LHS 0 vs RHS 1/4. Patch guidance D4 item 10 likewise."}], "non_blocking": [{"id": "N1", "decl": "omega0_ccr_descends, omegaP_ccr_descends", "fix": "Add [A,A] and [C,C] relation versions (omega0_ccr_descends_aa/_cc, omegaP_ccr_descends_aa/_cc)."}, {"id": "N2", "decl": "omegaP_*_right, omegaP_cross_*", "fix": "Generalize same-branch contractions to ν : Orientation and cross contractions to (ν, oppositeOrientation ν); add A_ν C_η = 0."}, {"id": "N3", "decl": "ordered_density_kernel et al., ground_*", "fix": "Optional: drop unused [NeZero (2*h)] / redundant hh."}, {"id": "N4", "decl": "bogoliubovMap_inverse", "fix": "Optional bogoliubovMap_inverse_iff with [NeZero M]."}, {"id": "N5", "decl": "A08 interface (CH20b)", "fix": "CH20b must add a coefficientwise PowerSeries extension of omegaP, Wick lemmas and a charge sector; optionally an orientation-parametrized oscDensity."}, {"id": "N6", "decl": "gramSum, compressed_no_vacuum_density", "fix": "None needed; document that complex coefficients and non-PSD ρ are stronger forms."}]}
```
