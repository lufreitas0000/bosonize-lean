## Adjudication verdict: CHANGES_REQUIRED

I checked every claim against the Core sources and also recomputed the key ones. I wrote an independent Python model of ω_P = ω₀∘β_{c,−s} on two-branch polynomials, with M=3 and (c,s)=(5/4,3/4). I tested the linter behaviour on the project toolchain (`lake env lean --stdin`, v4.35.0-rc4, lakefile has `-DwarningAsError=true`):
- An unused explicit hypothesis gives the warning "Variable name `h` is not explicitly referenced". With warnings as errors, that breaks the build.
- A named but unused instance binder gives no warning.
- A hypothesis that `omega` or `assumption` uses implicitly counts as used.

Core already contains the awkward workaround once (`have _ := hm` in `A07Interactions.bogoliubov_ccr_on_budget`, L1183).

The two issues that must be fixed now:
- **B1** is real: two theorems are false at ζ = 0.
- **N3** is real, but Reviewer 1 identified the wrong hypotheses. The ones that will actually break Phase B are in the four `ground_*` contraction lemmas, and Reviewer 1 missed them.

## Issue table
| id | R1 claim | my finding | class | reason |
|---|---|---|---|---|
| B1 | `density_kernel_diagonal` and `_pos` are false at ζ=0; adding hζ fixes them | **Confirmed.** `integerCharacter` is `ζ ^ (k*x)` (zpow, A01 L24), and in Lean 0^n = 0 for every integer n ≠ 0. So at ζ=0 with x.val≠0, ρ_R(x)=0. Numeric check at h=1, M=1, ζ=0, freePair, x=1: LHS = 0, RHS = 1/4, and `0 < 0` is false. With ζ≠0 the formula holds; at ζ=i, h=2, M=2, (5/4,3/4), x=y=3, both sides are 0.3984375. | PERTINENT | The statement as written is unprovable. |
| N1 | ccr_descends covers only [A,C]; add [A,A] and [C,C] | **Statements true.** ω₀ case: π of the relation is 0 by `osc_*_commute`. ω_P case: β_{c,−s}[A_p,A_q] = c²[A,A] − cs[A_p,C_q̄] − cs[C_p̄,A_q] + s²[C,C]. Under π the two middle terms cancel each other (δ_{p,q̄}=δ_{p̄,q}, and the weights are equal); they are not each 0 as R1 wrote, but R1's conclusion is right. 600 random checks of the form ω_P(a·r·b), r ∈ {aa, cc, ac}, gave 0 failures. | PERTINENT | Ledger claim c03 ("descends through the CCR ideal") is only partly covered. CH20b builds its CCR quotient / tensor star-algebra on A08 (N20 Def 20.4, Def 20.6 "preserves CCR"), so state descent needs all three relation types. Four cheap stubs. |
| N2 | Generalize contractions to ν and add A_R C_L = 0 | **All true.** Python check over both ν, all i,j < 3, eight orderings, cross pair with η = opposite ν: all pass. | DEFERRABLE | Ledger c07–c09 name only the right branch, and the guidance marks the left branch optional. CH20b's Gaussian moments go through *dressed* generators, where ω_P∘β_{c,s} = ω₀, so it needs ω₀ moments, not bare-left ω_P values. Left/general-ν lemmas can be added later in a new module without touching the frozen `_right` statements. |
| N3 | NeZero unused; hh redundant in ground_* | **R1's items are not linter hazards:** NeZero is an instance (not linted), and hh is passed to Core lemmas (`rho_lowering_budget_zero`, `ground_mem_budget`, `joint_signed_current_commutator` all take `hh`). **R1 missed the real hazards**, which no natural proof uses: `ground_lowering_raising.hn`; `ground_raising_lowering.{hm,hmM,hnM,hmargin}`; `ground_raising_raising.{hn,hmM,hnM,hmargin}`; `ground_lowering_lowering.{hm,hmM,hnM,hmargin}`. Then `M` itself is also unused in the last three. | PERTINENT, with R1's list replaced | ρ_{−n}Ω = 0 needs only hh, hN and 1 ≤ n (`rho_lowering_budget_zero` needs no margin). raising_raising goes through `rho_adjoint`, so only hm matters. In lowering_raising, the Schwinger coefficient gives 0 for m ≠ n with or without hn, and the margin bound \|−m\|+\|n\|+\|Ns r\| ≤ h comes from hmM, hnM and hmargin. |
| N4 | Add `bogoliubovMap_inverse_iff` with [NeZero M] | **True.** The composite is g ↦ (c²−s²)g; `FreeAlgebra.ι_ne_zero` exists in Mathlib (L523) and ℂ-modules have no zero smul divisors. [NeZero M] is necessary: at M=0 the generator set is empty and the composite is id for every (c,s). | DEFERRABLE | Nothing downstream uses it. It is an anti-vacuity check showing hcs is needed (ledger c04 says "iff"). Cheap; add it if convenient. |
| N5 | CH20b needs a series carrier, Wick lemmas and a charge sector | Agree | NOT PERTINENT (to CH19) | This is CH20b scope. |
| N6 | Documentation only | Agree | NOT PERTINENT | — |

## Additional issues found
1. **The real N3 hazards** in the four `ground_*` lemmas (above). Reviewer 1 missed these. The Core precedent `have _ := hm` (A07 L1183) shows this is exactly the awkward pattern to avoid.
2. **Logically redundant but used by the proof; I recommend keeping these.** No linter risk, and removing them would make Phase B harder:
   - `density_commutator_expectation.hζ`: the identity also holds at ζ=0 (checked numerically on all x,y ∈ ZMod 4). But the natural proof goes through `ordered_density_kernel`, which needs hζ.
   - `hh` in `ground_lowering_raising`, `excited_ket_norm_sq`, `ground_dressed_number`, `ground_dressed_reverse`, `ground_not_dressed_vacuum`, and the two `fock_ground_*` theorems: it is implied by marginAt with 1 ≤ m ≤ M (h ≥ 2M), but Core lemma calls consume it.
   - `hN` where hmargin is present: also used, through `ground_mem_budget`.
   - `density_kernel_diagonal_pos` has both `[NeZero (2*h)]` and `hh`, and the two `fock_ground_*` theorems have the same duplication. The prover will use hh (e.g. via `positivity`), so there is no warning. Dropping the instance is optional cosmetics.
3. Nothing else is false, unprovable or unsatisfiable. I re-verified:
   - the full contraction table, β inverse, the annihilation laws and the direction of the cross sign;
   - the ordered, commutator and symmetrized kernels, plus the s²/c² Luttinger identities;
   - `compressed_gram` = diag(2s², c², c²) entry by entry, the kernel argument, s=0 ⇒ e₀ in the kernel, and (5/3, 4/3) → (32/9, 25/9, 25/9);
   - the witness numbers 9/8, 25/8, −15/8, 51/2048, margin 4 ≤ 8, 2, 9/8, 3/256;
   - hζ is genuinely needed in `ordered_density_kernel`, `symmetrized_density_kernel`, `ordered_density_free` and `fock_ground_density_kernel` (each fails at ζ=0, x=y≠0);
   - all hypothesis sets are satisfiable by the concrete witness data.
4. Minor: patch guidance D4 item 10 and the ledger row for c15 to say "ζ ≠ 0". That is documentation only, not Lean.

## Change list for the revision round
1. **B1:**
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
   Optional: drop `[NeZero (2 * h)]` from both. Neither needs it, and `_pos` already has hh.
2. **N3a**, `ground_lowering_raising` (drop `hn`):
```lean
theorem ground_lowering_raising (h M : ℕ) (hh : 0 < h) (m n : ℕ)
    (hm : 1 ≤ m) (hmM : m ≤ M) (hnM : n ≤ M)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M 0 Ns branches.rightSpecies) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) *
         Bosonize.A05.rho h branches.rightSpecies (n : ℤ)) =
      if m = n then (m : ℂ) else 0 := by sorry
```
3. **N3b**, `ground_raising_lowering` (drop `M, hm, hmM, hnM, hmargin`):
```lean
theorem ground_raising_lowering (h : ℕ) (hh : 0 < h) (m n : ℕ) (hn : 1 ≤ n)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.rho h branches.rightSpecies (m : ℤ) *
         Bosonize.A05.rho h branches.rightSpecies (-(n : ℤ))) = 0 := by sorry
```
4. **N3c**, `ground_raising_raising` (drop `M, hn, hmM, hnM, hmargin`):
```lean
theorem ground_raising_raising (h : ℕ) (hh : 0 < h) (m n : ℕ) (hm : 1 ≤ m)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.rho h branches.rightSpecies (m : ℤ) *
         Bosonize.A05.rho h branches.rightSpecies (n : ℤ)) = 0 := by sorry
```
5. **N3d**, `ground_lowering_lowering` (drop `M, hm, hmM, hnM, hmargin`):
```lean
theorem ground_lowering_lowering (h : ℕ) (hh : 0 < h) (m n : ℕ) (hn : 1 ≤ n)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) *
         Bosonize.A05.rho h branches.rightSpecies (-(n : ℤ))) = 0 := by sorry
```
   No other declaration statement refers to these four, so nothing else needs to change.
6. **N1**, add to A08 after `omega0_ccr_descends` and `omegaP_ccr_descends`:
```lean
theorem omega0_ccr_descends_aa (M : ℕ) (a b : OscAlgebra M) (p q : OscMode M) :
    omega0 M (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (false, q) -
      FreeAlgebra.ι ℂ (false, q) * FreeAlgebra.ι ℂ (false, p)) * b) = 0 := by sorry
theorem omega0_ccr_descends_cc (M : ℕ) (a b : OscAlgebra M) (p q : OscMode M) :
    omega0 M (a * (FreeAlgebra.ι ℂ (true, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (true, p)) * b) = 0 := by sorry
theorem omegaP_ccr_descends_aa (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (a b : OscAlgebra M) (p q : OscMode M) :
    omegaP M hp (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (false, q) -
      FreeAlgebra.ι ℂ (false, q) * FreeAlgebra.ι ℂ (false, p)) * b) = 0 := by sorry
theorem omegaP_ccr_descends_cc (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (a b : OscAlgebra M) (p q : OscMode M) :
    omegaP M hp (a * (FreeAlgebra.ι ℂ (true, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (true, p)) * b) = 0 := by sorry
```
7. Optional, recommended because it is free: `bogoliubovMap_inverse_iff` (N4), signature below.

## Tracked warnings (deferrable items)
- **N2:** the general-ν same-branch table, the general (ν, oppositeOrientation ν) cross table, and the missing `A_ν C_η = 0` are all verified true. A later module (CH20b) can add them without changing frozen statements.
- **N4:** to be added later if not now:
```lean
theorem bogoliubovMap_inverse_iff (M : ℕ) [NeZero M] (c s : ℝ) :
    (bogoliubovMap M c s).comp (bogoliubovMap M c (-s)) = AlgHom.id ℂ (OscAlgebra M) ↔ c ^ 2 - s ^ 2 = 1
```
  [NeZero M] is required.
- **CH20b helper (optional):** `omegaP_comp_bogoliubovMap : (omegaP M hp).comp (bogoliubovMap M hp.c hp.s).toLinearMap = omega0 M`. It is one line from `bogoliubovMap_inverse_rev`, and it is the route to CH20b's Gaussian moments of dressed generators.
- **Kept on purpose:** `density_commutator_expectation.hζ` (logically redundant but used by the proof). Also `hh` and `hN` where hmargin is present (implied, but consumed by Core lemmas).
- `[NeZero (2*h)]` is unnecessary in several abstract theorems and duplicates hh in `_pos` and the `fock_ground_*` theorems. It is harmless, since instances are not linted.
- Patch guidance D4 item 10 and ledger c15 to include `ζ ≠ 0` (docs only).
- N5 (CH20b series carrier, Wick lemmas, charge sector) and N6: no action for CH19.

```json
{"verdict": "CHANGES_REQUIRED", "changes": [{"id": "B1", "change": "Add (hζ : ζ ≠ 0) after (ζ : ℂ) in density_kernel_diagonal and density_kernel_diagonal_pos (counterexample h=1,M=1,ζ=0,freePair,x=1: LHS 0 vs RHS 1/4). Optionally drop [NeZero (2*h)] from both."}, {"id": "N3a", "change": "ground_lowering_raising: remove explicit hypothesis (hn : 1 ≤ n); unused because schwingerCoefficient(-m,n)=0 for m≠n regardless and the margin comes from hmM/hnM/hmargin."}, {"id": "N3b", "change": "ground_raising_lowering: new signature (h : ℕ) (hh : 0 < h) (m n : ℕ) (hn : 1 ≤ n) (branches) (Ns) (hN); drop M, hm, hmM, hnM, hmargin (rho_lowering_budget_zero needs only hh, hN, 0<n)."}, {"id": "N3c", "change": "ground_raising_raising: new signature (h : ℕ) (hh : 0 < h) (m n : ℕ) (hm : 1 ≤ m) (branches) (Ns) (hN); drop M, hn, hmM, hnM, hmargin (proof via rho_adjoint and ρ_{-m}Ω=0)."}, {"id": "N3d", "change": "ground_lowering_lowering: new signature (h : ℕ) (hh : 0 < h) (m n : ℕ) (hn : 1 ≤ n) (branches) (Ns) (hN); drop M, hm, hmM, hnM, hmargin."}, {"id": "N1", "change": "Add omega0_ccr_descends_aa, omega0_ccr_descends_cc, omegaP_ccr_descends_aa, omegaP_ccr_descends_cc (ω(a*(g_p g_q - g_q g_p)*b)=0 for g both annihilators / both creators); verified true."}], "warnings": [{"id": "N2", "note": "General-ν and full cross-orientation contraction table (incl. A_ν C_η=0) verified true; deferrable since CH20b needs ω₀/dressed moments and can add these additively."}, {"id": "N4", "note": "bogoliubovMap_inverse_iff with [NeZero M] is true (FreeAlgebra.ι_ne_zero); anti-vacuity check for hcs; no downstream use; optional now."}, {"id": "N3-keep", "note": "density_commutator_expectation.hζ and hh/hN in margin-bearing Fock lemmas are logically redundant but consumed by the natural proof (no linter hazard); keep. [NeZero (2*h)] redundancies are harmless instances."}, {"id": "CH20b-helper", "note": "Consider omegaP_comp_bogoliubovMap : (omegaP M hp).comp (bogoliubovMap M hp.c hp.s).toLinearMap = omega0 M in CH20b."}, {"id": "guidance-D4.10", "note": "Patch guidance D4 item 10 / ledger c15 to include ζ ≠ 0 (docs only)."}, {"id": "N5-N6", "note": "No CH19 action."}]}
```
