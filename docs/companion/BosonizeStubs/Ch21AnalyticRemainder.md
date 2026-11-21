# Mirrored Companion: `BosonizeStubs.Ch21AnalyticSWCore` & `BosonizeStubs.Ch21AnalyticRemainder` (Chapter 21 Phase B)

**Lean Modules:** [`BosonizeStubs/Ch21AnalyticSWCore.lean`](../../../BosonizeStubs/Ch21AnalyticSWCore.lean) (leaf `module`, zero `Bosonize` dependencies) and [`BosonizeStubs/Ch21AnalyticRemainder.lean`](../../../BosonizeStubs/Ch21AnalyticRemainder.lean) (concrete `2×2` and `Ch21 → A10` Umklapp instantiations)  
**Parent Staging Modules:** [`BosonizeStubs/Ch21SpinfulModels.lean`](../../../BosonizeStubs/Ch21SpinfulModels.lean), [`BosonizeStubs/Ch21CocycleAndLeakage.lean`](../../../BosonizeStubs/Ch21CocycleAndLeakage.lean), [`BosonizeStubs/Ch21BudgetAndSWBridge.lean`](../../../BosonizeStubs/Ch21BudgetAndSWBridge.lean)  
**Reference LaTeX Section:** [`notes/latex/chapters/sections/21.4.tex`](../../../notes/latex/chapters/sections/21.4.tex) (L403–577: `prop:ch21-sw-analytic-remainder`, `ex:ch21-sw-two-level`)  
**Audit Reference:** [`docs/plans/v1-s9/v1_release_readiness_audit.md`](../../plans/v1-s9/v1_release_readiness_audit.md)  
**Phase Status:** Phase B Complete — Awaiting Human Phase C Promotion (`lake --wfail build Bosonize` and `lake --wfail build BosonizeStubs` both exit `0` with **zero warnings**; `lake env lean -DwarningAsError=true` exits `0` on both files with zero warnings and zero `sorry`s; `python3 scripts/webllm/audit_axioms.py BosonizeStubs/Ch21AnalyticSWCore.lean BosonizeStubs/Ch21AnalyticRemainder.lean` exits `0` across all `58` exported declarations — `25` in `Ch21AnalyticSWCore.lean` [`18` proofs: `7` `theorem`s + `11` `lemma`s; `7` `def`s; plus `3` `private lemma`s] and `33` in `Ch21AnalyticRemainder.lean` [`24` proofs: `12` `theorem`s + `12` `lemma`s; `9` data/instance commands: `5` `def`s + `4` `local instance`s; plus `4` `private lemma`s] — using standard axioms `[propext, Classical.choice, Quot.sound]` only).

---

## 1. Carrier Conventions & Module Split

Following the leaf-`module` pattern of [`Bosonize/Core/V1S5FiniteVectorStates.lean`](../../../Bosonize/Core/V1S5FiniteVectorStates.lean), the pure-Mathlib abstract Banach/`CStarRing` Taylor remainder core is placed in the `module` file `BosonizeStubs/Ch21AnalyticSWCore.lean` (`public import Mathlib.*`, `@[expose] public section`), while `BosonizeStubs/Ch21AnalyticRemainder.lean` imports only `BosonizeStubs.Ch21BudgetAndSWBridge` and `BosonizeStubs.Ch21AnalyticSWCore`. This keeps `lake --wfail build BosonizeStubs` strictly warning-free (`0` warnings) and ready for Phase C promotion into `Bosonize/Core/`.

| Convention | Lean Realization | Mathematical Meaning |
| :--- | :--- | :--- |
| Abstract Banach / `CStarRing` setting (`Ch21AnalyticSWCore`) | `[NormedRing A] [StarRing A] [CompleteSpace A] [CStarRing A] [NormedAlgebra ℝ A] [StarModule ℝ A]` | Unital complex/real Banach `C*`-normed algebra, instantiating simultaneously on `Matrix ι ι ℂ` with the Euclidean `L2Operator` norm (`Matrix.Norms.L2Operator`) and on bounded Hilbert-space operators `E →L[ℂ] E` (`A05.FockSpace SpinBranch h →L[ℂ] A05.FockSpace SpinBranch h`). |
| Iterated commutator & conjugation flow (`Ch21AnalyticSWCore`) | `adOp S1 T`, `adIter S1 n T`, `swAdjointFlow S1 r T` | $\operatorname{ad}_{S_1}(T) = [S_1, T]$, $\operatorname{ad}_{S_1}^n(T)$, and $\mathcal U_r(T) = e^{r S_1} T e^{-r S_1}$ via `NormedSpace.exp`. |
| Analytic rotated Hamiltonian & remainder (`Ch21AnalyticSWCore`) | `swRotatedHam H0 V S1 t`, `swBchPoly2 H0 V S1 t`, `swEffPoly2 P H0 V S1 t`, `swRemainder3 H0 V S1 t` | $\widetilde H(t) = \mathcal U_t(H_0 + t V)$, degree-2 BCH polynomial $B_2(t)$, compressed effective Hamiltonian $H_{\mathrm{eff}}^{[2]}(t)$, and analytic Taylor remainder $R_3(t) := \widetilde H(t) - B_2(t)$ (`eq:ch21-rem-definition`). |
| Explicit `2×2` witness carrier (`Ch21AnalyticRemainder`) | `A10.swCounterH0_2x2`, `swCounterV_2x2`, `swCounterS1_2x2`, `swCounterP_2x2` + `swCounterEigvalMinus`, `swCounterEigvalPlus`, `swCounterEigvecMinus`, `swCounterEigvecPlus` | Frozen Core `2×2` matrices on `Matrix (Fin 2) (Fin 2) ℂ` (`L2Operator` norm) with exact eigenvalues $E_\pm(t) = (1 \pm \sqrt{1 + 4 t^2})/2$ and globally nonzero eigenvectors $v_\pm(t)$ for all $t \in \mathbb R$. |
| Fock-space bounded-operator bridge (`Ch21AnalyticRemainder`) | `toFockCLM h`, `localModeLinearOrderCh21Rem`, `localModeLTCh21Rem`, `localModeLECh21Rem`, `localModeDecidableEqCh21Rem` | `LinearMap.toContinuousLinearMap` embedding `A05.Operators SpinBranch h` as a `*`-algebra into `A05.FockSpace SpinBranch h →L[ℂ] A05.FockSpace SpinBranch h`, aligning `swBchPoly2`/`swEffPoly2` verbatim with `A10.bchSecondOrderPolynomial`/`A10.swEffectiveSecondOrder`. |

---

## 2. Exported API, Hypotheses & Verification Inventory

### Part A (`BosonizeStubs/Ch21AnalyticSWCore.lean`, `25` exported declarations): Abstract Finite Analytic Schrieffer-Wolff Remainder (`prop:ch21-sw-analytic-remainder`)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `adOp`, `adIter` | `def` | `[NormedRing A] [NormedAlgebra ℝ A]` | Complete (0 `sorry`) | Commutator `[S₁, T]` and iterated adjoint `ad_{S₁}^n(T)`. |
| `swAdjointFlow`, `swRotatedHam`, `swBchPoly2`, `swEffPoly2`, `swRemainder3` | `def` | `[NormedRing A] [NormedAlgebra ℝ A]` | Complete (0 `sorry`) | $\mathcal U_r(T) = e^{r S_1} T e^{-r S_1}$, $\widetilde H(t) = \mathcal U_t(H_0 + t V)$, $B_2(t)$, $H_{\mathrm{eff}}^{[2]}(t)$, and $R_3(t) = \widetilde H(t) - B_2(t)$. |
| `swAdjointFlow_zero`, `swAdjointFlow_add`, `swAdjointFlow_smul` | `lemma` | `[NormedRing A] [NormedAlgebra ℝ A]` | Proved (0 `sorry`) | $\mathcal U_0(T) = T$ and $\mathbb R$-linearity of $\mathcal U_r$. |
| `swBchPoly2_compressed` | `theorem` | `P² = P`, `P + Q = 1`, `P Q = Q P = 0`, `P S₁ P = 0`, `[S₁, H₀] = -(P V Q + Q V P)` | Proved (0 `sorry`) | Algebraic degree-2 compressed BCH identity $P B_2(t) P = H_{\mathrm{eff}}^{[2]}(t)$ in any normed $\mathbb R$-algebra. |
| `hasDerivAt_swAdjointFlow`, `hasDerivAt_swAdjointFlow_scaled`, `continuous_swAdjointFlow_scaled` | `lemma` | `[NormedRing A] [CompleteSpace A] [NormedAlgebra ℝ A]` | Proved (0 `sorry`) | $\frac{d}{dr} \mathcal U_r(T) = \mathcal U_r([S_1, T])$, scaled derivative $\frac{d}{du} \mathcal U_{ut}(T) = t\,\mathcal U_{ut}([S_1, T])$, and continuity on $\mathbb R$. |
| `swAdjointFlow_taylor_order1`, `swAdjointFlow_taylor_order2` | `theorem` | `[NormedRing A] [CompleteSpace A] [NormedAlgebra ℝ A]` | Proved (0 `sorry`) | Order-1 and order-2 Taylor identities with integral remainder on `[0, 1]` proved directly via the Fundamental Theorem of Calculus (`intervalIntegral.integral_eq_sub_of_hasDerivAt`). |
| `swRemainder3_integral` | `theorem` | `[NormedRing A] [CompleteSpace A] [NormedAlgebra ℝ A]` | Proved (0 `sorry`) | Equation `eq:ch21-sw-integral-remainder`: $R_3(t) = \frac{t^3}{2}\int_0^1 (1-u)^2 \mathcal U_{ut}(\operatorname{ad}_{S_1}^3 H_0)\,du + t^3\int_0^1 (1-u) \mathcal U_{ut}(\operatorname{ad}_{S_1}^2 V)\,du$. |
| `exp_smul_of_sq_eq_neg_one` | `theorem` | `J * J = -1` | Proved (0 `sorry`) | Euler trigonometric exponential $e^{t J} = (\cos t)\,1 + (\sin t)\,J$ in any complete normed $\mathbb R$-algebra via ODE uniqueness. |
| `norm_ortho_proj_le_one`, `norm_compress_le_of_ortho_proj` | `lemma` | `[NormedRing A] [StarRing A] [CStarRing A]`, `P² = P = P†` | Proved (0 `sorry`) | Orthogonal projection contraction `‖P‖ ≤ 1` and compressed norm bound `‖P R P‖ ≤ ‖R‖`. |
| `exp_smul_skew_mem_unitary`, `norm_exp_smul_skew_eq_one`, `swAdjointFlow_norm_eq` | `lemma` | `star S₁ = -S₁` (plus `[Nontrivial A]` for `‖e^{r S₁}‖ = 1`) | Proved (0 `sorry`) | Unitarity $e^{r S_1} \in \mathrm{unitary}(A)$, unit norm `‖e^{r S₁}‖ = 1`, and unitary invariance `‖𝒰_r(T)‖ = ‖T‖`. |
| `swRemainder3_norm_bound` | `theorem` | `star S₁ = -S₁` | Proved (0 `sorry`) | Equation `eq:ch21-sw-norm-bound` (uncompressed): `‖R₃(t)‖ ≤ |t|³ (‖ad_{S₁}³ H₀‖ / 6 + ‖ad_{S₁}² V‖ / 2)`. |
| `swCompressed_exact_plus_remainder_and_bound` | `theorem` | `P² = P = P†`, `P + Q = 1`, `P Q = Q P = 0`, `P S₁ P = 0`, `S₁† = -S₁`, `[S₁, H₀] = -(P V Q + Q V P)` | Proved (0 `sorry`) | Full Proposition `prop:ch21-sw-analytic-remainder`: exact decomposition $P \widetilde H(t) P = H_{\mathrm{eff}}^{[2]}(t) + P R_3(t) P$ (`eq:ch21-sw-exact-plus-remainder`) and norm chain `‖P R₃(t) P‖ ≤ ‖R₃(t)‖ ≤ |t|³ (‖ad_{S₁}³ H₀‖ / 6 + ‖ad_{S₁}² V‖ / 2)`. |

### Part B (`BosonizeStubs/Ch21AnalyticRemainder.lean`, `33` exported declarations): Explicit `2×2` Witness (`ex:ch21-sw-two-level`) & `Ch21 → A10` Umklapp Instantiation

#### Section 2: Explicit `2×2` Analytic Schrieffer-Wolff Witness (`ex:ch21-sw-two-level`)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `swCounterEigvalMinus`, `swCounterEigvalPlus`, `swCounterEigvecMinus`, `swCounterEigvecPlus` | `def` | `t : ℝ` | Complete (0 `sorry`) | Exact eigenvalues $E_\pm(t) = (1 \pm \sqrt{1 + 4 t^2})/2$ and globally nonzero eigenvectors $v_-(t) = [-(1+\sqrt{1+4t^2}), 2t]$, $v_+(t) = [2t, 1+\sqrt{1+4t^2}]$. |
| `swCounterS1_2x2_sq`, `swCounterS1_2x2_skew`, `swCounterP_2x2_ortho` | `lemma` | None | Proved (0 `sorry`) | $S_1^2 = -I$, $S_1^\dagger = -S_1$, and $P^2 = P = P^\dagger$ on frozen `A10.swCounter*_2x2`. |
| `swCounter_2x2_exp_eq`, `swCounter_2x2_exp_neg_eq` | `theorem` | `t : ℝ` | Proved (0 `sorry`) | Closed trigonometric rotation matrices $e^{\pm t S_1} = \begin{pmatrix}\cos t & \mp\sin t \\ \pm\sin t & \cos t\end{pmatrix}$. |
| `swCounter_2x2_rotated_entries` | `theorem` | `t : ℝ` | Proved (0 `sorry`) | Exact compressed entry $(P \widetilde H(t) P)_{00} = \sin^2 t - t \sin(2t)$ (`eq:ch21-sw-2x2-rotated`), off-diagonal entry $(\widetilde H(t))_{01} = t \cos(2t) - \frac{1}{2}\sin(2t)$ (`eq:ch21-sw-2x2-off`), and $(H_{\mathrm{eff}}^{[2]}(t))_{00} = -t^2$. |
| `swCounter_2x2_exact_eigenvalues` | `theorem` | `t : ℝ` | Proved (0 `sorry`) | Equation `eq:ch21-sw-2x2-eigvals`: for all $t \in \mathbb R$, $v_\pm(t) \ne 0$ and $(H_0 + t V) v_\pm(t) = E_\pm(t) v_\pm(t)$. |
| `swCounter_2x2_finite_coupling_discrepancy` | `theorem` | None | Proved (0 `sorry`) | Exact discrepancy at $t = 2/3$: $E_-(2/3) = -1/3$, $E_+(2/3) = 4/3$, $(H_{\mathrm{eff}}^{[2]}(2/3))_{00} = -4/9$, and $-1/3 \ne -4/9$. |
| `swCounter_2x2_analytic_remainder_bound` | `theorem` | `t : ℝ` | Proved (0 `sorry`) | Concrete instantiation on `A10.swCounter*_2x2`: `‖P R₃(t) P‖ ≤ ‖R₃(t)‖ ≤ (8 / 3) * |t|³` in the `L2Operator` norm. |

#### Section 3: Concrete `Ch21 → A10` Spinful Umklapp Block Analytic Remainder Bounds

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `localModeLinearOrderCh21Rem`, `localModeLTCh21Rem`, `localModeLECh21Rem`, `localModeDecidableEqCh21Rem` | `local instance` | `h : ℕ` | Complete (0 `sorry`) | Lexicographic `A05.speciesOrder h` instances matching `A05`/`Ch14`/`Ch21BudgetAndSWBridge`. |
| `toFockCLM` | `def` | `h : ℕ, T : A05.Operators SpinBranch h` | Complete (0 `sorry`) | `LinearMap.toContinuousLinearMap T` in `A05.FockSpace SpinBranch h →L[ℂ] A05.FockSpace SpinBranch h`. |
| `toFockCLM_add`, `toFockCLM_sub`, `toFockCLM_neg`, `toFockCLM_zero`, `toFockCLM_one`, `toFockCLM_mul`, `toFockCLM_smul_real`, `toFockCLM_star`, `toFockCLM_commutator` | `lemma` | `h : ℕ` | Proved (0 `sorry`) | Unital real-linear `*`-algebra homomorphism laws bridging `A05.Operators` and `LinearMap.adjoint` to `A05.FockSpace →L[ℂ] A05.FockSpace` and `star`. |
| `toFockCLM_bchSecondOrderPolynomial`, `toFockCLM_swEffectiveSecondOrder` | `theorem` | `h : ℕ, t : ℝ` | Proved (0 `sorry`) | Exact equality of `swBchPoly2` / `swEffPoly2` with `toFockCLM h (A10.bchSecondOrderPolynomial ...)` / `toFockCLM h (A10.swEffectiveSecondOrder ...)`. |
| `norm_toFockCLM_umklappBlockVOp` | `theorem` | `0 < h, gU : ℝ` | Proved (0 `sorry`) | Exact Hilbert-space operator norm `‖toFockCLM h (umklappBlockVOp h hh gU)‖ = |g_U| / (4 h²)` via the `C*`-identity on `V² = c² Π_block`. |
| `umklappBlock_iterated_ad` | `theorem` | `0 < h, gU : ℝ` | Proved (0 `sorry`) | Exact iterated commutators `ad_{S₁}²(V) = (-4 s²) • V` and `ad_{S₁}³(H₀) = (4 s²) • V` with `s = -g_U / (8 h³)`. |
| `umklappBlock_analytic_remainder_bound` | `theorem` | `0 < h, gU t : ℝ` | Proved (0 `sorry`) | Direct operator-level instantiation on `umklappBlock_a10_bch_bridge`: $P \widetilde H(t) P = \mathrm{toFockCLM}(H_{\mathrm{eff}}^{[2]}(t)) + P R_3(t) P$ and `‖P R₃(t) P‖ ≤ ‖R₃(t)‖ ≤ |t|³ |g_U|³ / (96 h⁸)`. |
| `umklappBlock_analytic_remainder_bound_h2` | `theorem` | `gU t : ℝ` | Proved (0 `sorry`) | Concrete `h = 2` specialization: `‖P R₃(t) P‖ ≤ ‖R₃(t)‖ ≤ |t|³ |g_U|³ / 24576`. |

---

## 3. Epistemic Scope Note

Following Remark `21.4.tex` L482–489, every remainder estimate across `Ch21AnalyticSWCore` and `Ch21AnalyticRemainder` is a **finite-carrier** estimate at fixed `h` (`|t|³ |g_U|³ / (96 h⁸)` on the isolated 2-state Umklapp block, `(8/3)|t|³` on the 2-level counterexample). It does **not** prove a uniform-in-$L$ thermodynamic perturbative expansion or continuum RG scaling (`thm:ch21-umklapp-spin-cancel`, `thm:ch21-scaling-dimension-mott`).

---

## 4. Verification Summary

- `lake --wfail build Bosonize`: exit `0` (`0` warnings across all `44` Core files).
- `lake --wfail build BosonizeStubs`: exit `0` (`Build completed successfully (3463 jobs)`, `0` warnings across all `5` Ch21 staging files).
- `lake env lean -DwarningAsError=true BosonizeStubs/Ch21AnalyticSWCore.lean`: exit `0` (zero warnings, zero errors, zero `sorry`s).
- `lake env lean -DwarningAsError=true BosonizeStubs/Ch21AnalyticRemainder.lean`: exit `0` (zero warnings, zero errors, zero `sorry`s).
- `python3 scripts/webllm/audit_axioms.py BosonizeStubs/Ch21AnalyticSWCore.lean BosonizeStubs/Ch21AnalyticRemainder.lean`: exit `0` (`PASS: 58 freshly built data/theorem declarations` = `25` + `33`, standard axioms `[propext, Classical.choice, Quot.sound]` only).
- `python3 scripts/guards/core_lock.py`: exit `0` (`44` Core files untouched).
- `python3 -m unittest discover -s scripts/guards -p 'test_*.py'`: exit `0` (`69` tests).
- `python3 -m unittest discover -s scripts/webllm -p 'test_*.py'`: exit `0` (`20` tests).
- `python3 scripts/check_book_sources.py`: exit `0`.
- `python3 /home/lu/Projects/scripts/uow.py check --repo bosonize-lean`: exit `0`.
- `python3 scripts/guards/stub_lock.py --check --strict`: exit `1` (expected: only the five unbaselined Phase B `BosonizeStubs/Ch21*.lean` staging files, awaiting human Phase C review).
