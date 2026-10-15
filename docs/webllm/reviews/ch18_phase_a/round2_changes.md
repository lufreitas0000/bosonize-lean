# CH18 Phase A — revision round 2: required changes (Reviewer 2 adjudication, 2026-10-14 20:45)

Two independent reviews (R1 FAIL; R2 adjudication CHANGES_REQUIRED) confirmed that all 28 current theorem statements are true and provable from the frozen Core. The changes below strengthen or complete the interface before it is frozen. Apply EXACTLY these changes and keep everything else unchanged: every other declaration, statement, hypothesis, docstring and section. Return the complete Markdown file in the same envelope.

Core facts (verified):
- `Bosonize.A07Interactions.oppositeOrientation` (A07 L64): `.right ↦ .left`, `.left ↦ .right`.
- `Bosonize.A05.rho_cross_commute (h) (ν η : σ) (hne : ν ≠ η) (m n : ℤ)` is global.
- `Bosonize.A06.joint_signed_current_commutator` needs `|m|+|n|+K+|Ns ν| ≤ h`.

1. **Module layout (N8).** Remove the `BosonizeStubs/A08Ch18Scalars.lean` markers. Put ALL declarations in ONE module, `-- BEGIN_MODULE BosonizeStubs/Ch18Bogoliubov.lean` … `-- END_MODULE BosonizeStubs/Ch18Bogoliubov.lean`: scalar section first, then `variable {σ : Type*} [Fintype σ] [LinearOrder σ]` before the operator section. Update the Source map / Design / Review prose that names module paths. (Reason: `A08…` would freeze a pseudo-appendix Core file upstream of the real Appendix A08.)
2. **B1.** REPLACE `bogoliubov_cross_annihilator_creator_on_budget` by the global statement:
   `theorem bogoliubov_cross_annihilator_creator (h m : ℕ) (c s : ℝ) (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) : Bosonize.A02.commutator (Bosonize.A07Interactions.bogoliubovAnnihilator h m c s branches η) (Bosonize.A07Interactions.bogoliubovCreator h m c s branches (Bosonize.A07Interactions.oppositeOrientation η)) = 0 := by sorry`
3. **B2.** ADD (operator section, next to `bogoliubov_cross_creator_creator_on_budget`):
   `theorem bogoliubov_cross_annihilator_annihilator_on_budget (h M K m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (c s : ℝ) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ) (hmargin : Bosonize.A06.branchMargins h M K Ns branches) (v : Bosonize.A05.FockSpace σ h) (hv : v ∈ Bosonize.A05.jointBudget h Ns K) : Bosonize.A02.commutator (Bosonize.A07Interactions.bogoliubovAnnihilator h m c s branches .right) (Bosonize.A07Interactions.bogoliubovAnnihilator h m c s branches .left) v = 0 := by sorry`
4. **N9 (needed by the A08/A09 drafts).** ADD to the scalar section:
   `abbrev LuttingerParams (v1 v2 : ℝ) := Bosonize.A07Interactions.HyperbolicParams v1 v2`
   `def LuttingerParams.toHyperbolicPair {v1 v2 : ℝ} (lp : LuttingerParams v1 v2) : HyperbolicPair := HyperbolicPair.ofParams lp`
5. **N2c (needed by CH19).** ADD:
   `theorem luttingerGInv_eq_inv (hp : HyperbolicPair) : luttingerGInv hp = (luttingerG hp)⁻¹ := by sorry`
   `theorem hyperbolic_coeff_eq_luttinger (hp : HyperbolicPair) : hp.c ^ 2 + hp.s ^ 2 = (luttingerG hp + (luttingerG hp)⁻¹) / 2 := by sorry`
6. **A1 (needed by CH19/A08 on the polynomial carrier).** ADD, with a docstring saying it is the carrier-independent Lemma 18.3 for reuse on other carriers:
   `theorem HyperbolicPair.inverse_combination {E : Type*} [AddCommGroup E] [Module ℂ E] (hp : HyperbolicPair) (X Y : E) : (hp.c : ℂ) • ((hp.c : ℂ) • X + (hp.s : ℂ) • Y) - (hp.s : ℂ) • ((hp.c : ℂ) • Y + (hp.s : ℂ) • X) = X := by sorry`
7. **N1.** ADD `theorem tanh_relation_of_params {v1 v2 : ℝ} (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) : v2 * (hp.c ^ 2 + hp.s ^ 2) = v1 * (2 * hp.c * hp.s) := by sorry`
8. **N2a.** ADD `theorem luttingerG_eq_sqrt_of_params {v1 v2 : ℝ} (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) : luttingerG (HyperbolicPair.ofParams hp) = Real.sqrt ((v1 - v2) / (v1 + v2)) := by sorry`
9. **N7.** DELETE the unused `vacuumShiftOp` definition (and any prose mentioning it).
10. **N11.** APPEND two conjuncts to `concrete_bogoliubov_witness`: `∧ luttingerG concretePair = 1 / 4 ∧ 2 * concreteParams.u * concreteParams.s ^ 2 = 9`.
11. Keep everything else unchanged, including `bogoliubov_cross_creator_creator_on_budget` with its `hm`, `u_lt_v1_of_v2_ne_zero` with `hv1`, and `no_common_bare_dressed_vacuum` with `hdressL`. Keep every data definition complete (no `sorry` in data), keep the `noncomputable` markers, and keep every theorem ending exactly `:= by sorry`.

Only these two declarations may disappear: `bogoliubov_cross_annihilator_creator_on_budget` (replaced, item 2) and `vacuumShiftOp` (deleted, item 9). Any other missing declaration rejects the revision automatically.

Tracked warnings, NOT to be changed now:
- N2b: `luttingerG < 1 ↔ 0 < v2`.
- N3: closed-form ΔE and `0 < ΔE ↔ v2 ≠ 0`.
- N4: `u = √(v1²−v2²)`.
- N5, N6, N12: redundant hypotheses mirroring the sources/Core.
- N10: ground theorems for arbitrary (c,s).
- N13: source-map citation of `bogoliubov_creator_adjoint`.
