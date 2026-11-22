# Mirrored Companion: `BosonizeStubs.Ch21AnalyticSWCore` (Chapter 21 Phase B Leaf Module)

**Lean Module:** [`BosonizeStubs/Ch21AnalyticSWCore.lean`](../../../BosonizeStubs/Ch21AnalyticSWCore.lean) (leaf `module`, zero `Bosonize` dependencies)  
**Downstream Instantiation Module:** [`BosonizeStubs/Ch21AnalyticRemainder.lean`](../../../BosonizeStubs/Ch21AnalyticRemainder.lean) ([`Ch21AnalyticRemainder.md`](Ch21AnalyticRemainder.md))  
**Reference LaTeX Section:** [`notes/latex/chapters/sections/21.4.tex`](../../../notes/latex/chapters/sections/21.4.tex) (L313–326: `thm:ch21-sw-compressed`; L404–491: `subsec:ch21-sw-remainder`, `prop:ch21-sw-analytic-remainder`, `eq:ch21-rem-definition`, `eq:ch21-sw-exact-plus-remainder`, `eq:ch21-sw-integral-remainder`, `eq:ch21-sw-norm-bound`; L495–545: `ex:ch21-sw-two-level`)  
**Audit Reference:** [`docs/plans/v1-s9/v1_release_readiness_audit.md`](../../plans/v1-s9/v1_release_readiness_audit.md)  
**Phase Status:** Phase B Complete — Awaiting Human Phase C Promotion (`lake --wfail build BosonizeStubs` and `lake env lean -DwarningAsError=true BosonizeStubs/Ch21AnalyticSWCore.lean` exit `0` with zero warnings and zero `sorry`s; `python3 scripts/webllm/audit_axioms.py BosonizeStubs/Ch21AnalyticSWCore.lean` exits `0` across all `25` exported declarations [`18` exported proofs: `7` `theorem`s + `11` `lemma`s; `7` exported data commands: `7` `def`s; plus `3` `private lemma`s] using standard axioms `[propext, Classical.choice, Quot.sound]` only).

---

## 1. Carrier Conventions & Module Architecture

Following the leaf-`module` pattern of [`Bosonize/Core/V1S5FiniteVectorStates.lean`](../../../Bosonize/Core/V1S5FiniteVectorStates.lean), `BosonizeStubs/Ch21AnalyticSWCore.lean` is a pure-Mathlib Lean 4 `module` (`public import Mathlib.*`, `@[expose] public section`) with zero `Bosonize` imports. This allows downstream [`BosonizeStubs/Ch21AnalyticRemainder.lean`](../../../BosonizeStubs/Ch21AnalyticRemainder.lean) to import both frozen non-`module` Core (`Ch21BudgetAndSWBridge`) and `Mathlib` Banach/`CStarRing` analysis cleanly with zero Lake module-system warnings (`lake --wfail build BosonizeStubs` exit `0`).

| Convention | Lean Realization | Mathematical Meaning |
| :--- | :--- | :--- |
| Algebraic normed setting | `[NormedRing A] [NormedAlgebra ℝ A]` | General unital normed $\mathbb{R}$-algebra for commutator algebra and compressed BCH polynomial `swBchPoly2_compressed`. |
| Complete calculus setting | `[NormedRing A] [CompleteSpace A] [NormedAlgebra ℝ A]` | Complete normed $\mathbb{R}$-algebra supporting `NormedSpace.exp`, `HasDerivAt`, Fundamental Theorem of Calculus (`intervalIntegral`), and Euler trigonometric exponentials. |
| Unital `C*`-normed setting | `[NormedRing A] [StarRing A] [CStarRing A]` (+ `[CompleteSpace A] [NormedAlgebra ℝ A] [StarModule ℝ A]`) | Abstract Banach `C*`-algebra instantiating simultaneously on `Matrix ι ι ℂ` (`L2Operator` norm) and Hilbert-space operators `E →L[ℂ] E` (`A05.FockSpace SpinBranch h →L[ℂ] A05.FockSpace SpinBranch h`). |
| Iterated commutator & conjugation flow | `adOp S1 T`, `adIter S1 n T`, `swAdjointFlow S1 r T` | $\operatorname{ad}_{S_1}(T) = [S_1, T] = S_1 T - T S_1$, $\operatorname{ad}_{S_1}^n(T)$, and $\mathcal{U}_r(T) = e^{r S_1} T e^{-r S_1}$. |
| Rotated Hamiltonian, BCH polynomial & remainder | `swRotatedHam H0 V S1 t`, `swBchPoly2 H0 V S1 t`, `swEffPoly2 P H0 V S1 t`, `swRemainder3 H0 V S1 t` | $\widetilde{H}(t) = \mathcal{U}_t(H_0 + t V)$, degree-2 BCH polynomial $B_2(t)$, compressed effective Hamiltonian $H_{\mathrm{eff}}^{[2]}(t)$, and Taylor remainder $R_3(t) := \widetilde{H}(t) - B_2(t)$ (`eq:ch21-rem-definition`). |

---

## 2. Exported API, Hypotheses & Verification Inventory (`25` exported declarations)

### Section 1A: Abstract Definitions & Compressed BCH Identity (`AbstractAnalyticSWDefs`)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `adOp` | `def` | `[NormedRing A] [NormedAlgebra ℝ A], S1 T : A` | Complete (0 `sorry`) | Commutator `S1 * T - T * S1` ($\operatorname{ad}_{S_1}(T)$). |
| `adIter` | `def` | `[NormedRing A] [NormedAlgebra ℝ A], S1 : A, n : ℕ, T : A` | Complete (0 `sorry`) | Recursive iterated adjoint $\operatorname{ad}_{S_1}^n(T)$ (`0 ↦ T`, `n + 1 ↦ adOp S1 (adIter S1 n T)`). |
| `swAdjointFlow` | `def` | `[NormedRing A] [NormedAlgebra ℝ A], S1 : A, r : ℝ, T : A` | Complete (0 `sorry`) | One-parameter conjugation flow $\mathcal{U}_r(T) = \exp(r S_1) T \exp(-r S_1)$. |
| `swRotatedHam` | `def` | `[NormedRing A] [NormedAlgebra ℝ A], H0 V S1 : A, t : ℝ` | Complete (0 `sorry`) | Exact rotated Hamiltonian $\widetilde{H}(t) = \mathcal{U}_t(H_0 + t V)$. |
| `swBchPoly2` | `def` | `[NormedRing A] [NormedAlgebra ℝ A], H0 V S1 : A, t : ℝ` | Complete (0 `sorry`) | Degree-2 BCH polynomial $B_2(t) = H_0 + t(V + [S_1, H_0]) + t^2([S_1, V] + \frac{1}{2}\operatorname{ad}_{S_1}^2 H_0)$ matching `A10.bchSecondOrderPolynomial`. |
| `swEffPoly2` | `def` | `[NormedRing A] [NormedAlgebra ℝ A], P H0 V S1 : A, t : ℝ` | Complete (0 `sorry`) | Compressed effective Hamiltonian $H_{\mathrm{eff}}^{[2]}(t) = P H_0 P + t P V P + \frac{t^2}{2} P [S_1, V] P$ matching `A10.swEffectiveSecondOrder`. |
| `swRemainder3` | `def` | `[NormedRing A] [NormedAlgebra ℝ A], H0 V S1 : A, t : ℝ` | Complete (0 `sorry`) | Analytic Taylor remainder $R_3(t) := \widetilde{H}(t) - B_2(t)$ (`eq:ch21-rem-definition`). |
| `swAdjointFlow_zero` | `lemma` | `[NormedRing A] [NormedAlgebra ℝ A], S1 T : A` | Proved (0 `sorry`) | `@[simp]`: `swAdjointFlow S1 0 T = T`. |
| `swAdjointFlow_add` | `lemma` | `[NormedRing A] [NormedAlgebra ℝ A], S1 : A, r : ℝ, T₁ T₂ : A` | Proved (0 `sorry`) | Additivity `swAdjointFlow S1 r (T₁ + T₂) = swAdjointFlow S1 r T₁ + swAdjointFlow S1 r T₂`. |
| `swAdjointFlow_smul` | `lemma` | `[NormedRing A] [NormedAlgebra ℝ A], S1 : A, r c : ℝ, T : A` | Proved (0 `sorry`) | $\mathbb{R}$-homogeneity `swAdjointFlow S1 r (c • T) = c • swAdjointFlow S1 r T`. |
| `swBchPoly2_compressed` | `theorem` | `P * P = P`, `P + Q = 1`, `P * Q = 0`, `Q * P = 0`, `P * S1 * P = 0`, `adOp S1 H0 = -(P * V * Q + Q * V * P)` | Proved (0 `sorry`) | Algebraic degree-2 compressed BCH identity `P * swBchPoly2 H0 V S1 t * P = swEffPoly2 P H0 V S1 t` matching `thm:ch21-sw-compressed` / `A10.sw_compressed_bch_second_order`. |

### Section 1B: FTC Integral Taylor Remainder & Euler Formula (`AbstractAnalyticSWCalculus`)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `hasDerivAt_swAdjointFlow` | `lemma` | `[NormedRing A] [CompleteSpace A] [NormedAlgebra ℝ A], S1 T : A, r : ℝ` | Proved (0 `sorry`) | $\frac{d}{dr}\mathcal{U}_r(T) = \mathcal{U}_r([S_1, T])$. |
| `hasDerivAt_swAdjointFlow_scaled` | `lemma` | `[NormedRing A] [CompleteSpace A] [NormedAlgebra ℝ A], S1 T : A, t u : ℝ` | Proved (0 `sorry`) | Scaled derivative $\frac{d}{du}\mathcal{U}_{ut}(T) = t\,\mathcal{U}_{ut}([S_1, T])$. |
| `continuous_swAdjointFlow_scaled` | `lemma` | `[NormedRing A] [CompleteSpace A] [NormedAlgebra ℝ A], S1 T : A, t : ℝ` | Proved (0 `sorry`) | Continuity of $u \mapsto \mathcal{U}_{ut}(T)$ on $\mathbb{R}$. |
| `swAdjointFlow_taylor_order1` | `theorem` | `[NormedRing A] [CompleteSpace A] [NormedAlgebra ℝ A], S1 V : A, t : ℝ` | Proved (0 `sorry`) | Order-1 Taylor identity $\mathcal{U}_t(V) = V + t[S_1, V] + t^2 \int_0^1 (1 - u)\,\mathcal{U}_{ut}(\operatorname{ad}_{S_1}^2 V)\,du$ via FTC. |
| `swAdjointFlow_taylor_order2` | `theorem` | `[NormedRing A] [CompleteSpace A] [NormedAlgebra ℝ A], S1 H0 : A, t : ℝ` | Proved (0 `sorry`) | Order-2 Taylor identity $\mathcal{U}_t(H_0) = H_0 + t[S_1, H_0] + \frac{t^2}{2}\operatorname{ad}_{S_1}^2 H_0 + \frac{t^3}{2}\int_0^1 (1 - u)^2\,\mathcal{U}_{ut}(\operatorname{ad}_{S_1}^3 H_0)\,du$ via FTC. |
| `swRemainder3_integral` | `theorem` | `[NormedRing A] [CompleteSpace A] [NormedAlgebra ℝ A], H0 V S1 : A, t : ℝ` | Proved (0 `sorry`) | Equation `eq:ch21-sw-integral-remainder`: $R_3(t) = \frac{t^3}{2}\int_0^1 (1 - u)^2\,\mathcal{U}_{ut}(\operatorname{ad}_{S_1}^3 H_0)\,du + t^3\int_0^1 (1 - u)\,\mathcal{U}_{ut}(\operatorname{ad}_{S_1}^2 V)\,du$. |
| `exp_smul_of_sq_eq_neg_one` | `theorem` | `[NormedRing A] [CompleteSpace A] [NormedAlgebra ℝ A], J * J = -1, t : ℝ` | Proved (0 `sorry`) | Euler trigonometric exponential $\exp(t J) = (\cos t) 1 + (\sin t) J$ via ODE uniqueness (used for `ex:ch21-sw-two-level`). |

### Section 1C: `CStarRing` Contraction, Unitarity & Operator-Norm Remainder Bounds (`AbstractAnalyticSWCStar`, `AbstractAnalyticSWBounds`)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `norm_ortho_proj_le_one` | `lemma` | `[NormedRing A] [StarRing A] [CStarRing A], P * P = P, star P = P` | Proved (0 `sorry`) | Orthogonal projection contraction `‖P‖ ≤ 1` from `‖P‖² = ‖P* P‖ = ‖P‖`. |
| `norm_compress_le_of_ortho_proj` | `lemma` | `[NormedRing A] [StarRing A] [CStarRing A], P * P = P, star P = P, R : A` | Proved (0 `sorry`) | Compression contraction `‖P * R * P‖ ≤ ‖R‖`. |
| `exp_smul_skew_mem_unitary` | `lemma` | `[NormedRing A] [StarRing A] [CompleteSpace A] [CStarRing A] [NormedAlgebra ℝ A] [StarModule ℝ A], star S1 = -S1, r : ℝ` | Proved (0 `sorry`) | `NormedSpace.exp (r • S1) ∈ unitary A` for skew-adjoint `S₁`. |
| `norm_exp_smul_skew_eq_one` | `lemma` | `[Nontrivial A], star S1 = -S1, r : ℝ` | Proved (0 `sorry`) | Unit norm `‖NormedSpace.exp (r • S1)‖ = 1` in any nontrivial `CStarRing`. |
| `swAdjointFlow_norm_eq` | `lemma` | `star S1 = -S1, r : ℝ, T : A` | Proved (0 `sorry`) | Exact unitary norm invariance `‖swAdjointFlow S1 r T‖ = ‖T‖`. |
| `swRemainder3_norm_bound` | `theorem` | `star S1 = -S1, t : ℝ` | Proved (0 `sorry`) | Equation `eq:ch21-sw-norm-bound` (uncompressed): `‖R₃(t)‖ ≤ \|t\|³ * (‖adIter S1 3 H0‖ / 6 + ‖adIter S1 2 V‖ / 2)`. |
| `swCompressed_exact_plus_remainder_and_bound` | `theorem` | `P * P = P`, `star P = P`, `P + Q = 1`, `P * Q = 0`, `Q * P = 0`, `P * S1 * P = 0`, `star S1 = -S1`, `adOp S1 H0 = -(P * V * Q + Q * V * P)` | Proved (0 `sorry`) | Full Proposition `prop:ch21-sw-analytic-remainder`: `P * swRotatedHam H0 V S1 t * P = swEffPoly2 P H0 V S1 t + P * swRemainder3 H0 V S1 t * P` (`eq:ch21-sw-exact-plus-remainder`), `‖P * R₃(t) * P‖ ≤ ‖R₃(t)‖`, and `‖R₃(t)‖ ≤ \|t\|³ (‖ad_{S₁}³ H₀‖/6 + ‖ad_{S₁}² V‖/2)`. |

*(Note: `BosonizeStubs/Ch21AnalyticSWCore.lean` also contains `3` helper `private lemma`s — `hasDerivAt_one_sub`, `integral_one_sub_sq`, `integral_one_sub` — which are file-local and excluded from the exported API.)*

---

## 3. Epistemic Scope Note

Following `21.4.tex` L482–489, every estimate proved in `BosonizeStubs/Ch21AnalyticSWCore.lean` applies to **fixed finite-carrier** or **unital `CStarRing`** operators (`Matrix ι ι ℂ` with `L2Operator` norm or `E →L[ℂ] E` on finite-dimensional Hilbert spaces). It does **not** prove a uniform-in-$L$ thermodynamic perturbative expansion or continuum RG scaling.

---

## 4. Verification Summary

- `lake --wfail build BosonizeStubs`: exit `0` (`0` warnings across all `5` Ch21 staging modules).
- `lake env lean -DwarningAsError=true BosonizeStubs/Ch21AnalyticSWCore.lean`: exit `0` (zero warnings, zero errors, zero `sorry`s).
- `python3 scripts/webllm/audit_axioms.py BosonizeStubs/Ch21AnalyticSWCore.lean`: exit `0` (`25` exported declarations, standard axioms `[propext, Classical.choice, Quot.sound]` only).
- `python3 scripts/guards/core_lock.py`: exit `0` (`44` Core files untouched).
- `python3 -m unittest discover -s scripts/guards -p 'test_*.py'`: exit `0` (`69` tests).
- `python3 scripts/check_book_sources.py`: exit `0`.
- `python3 /home/lu/Projects/scripts/uow.py check --repo bosonize-lean`: exit `0`.
