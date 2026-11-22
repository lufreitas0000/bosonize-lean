# Mirrored Companion: `BosonizeStubs.Ch21CocycleAndLeakage` (Chapter 21 Phase B)

**Lean Module:** [`BosonizeStubs/Ch21CocycleAndLeakage.lean`](../../../BosonizeStubs/Ch21CocycleAndLeakage.lean)  
**Parent Staging Module:** [`BosonizeStubs/Ch21SpinfulModels.lean`](../../../BosonizeStubs/Ch21SpinfulModels.lean)  
**Reference LaTeX Sections:** [`notes/latex/chapters/sections/21.1.tex`](../../../notes/latex/chapters/sections/21.1.tex) (L340–401, L496–574, L633–802), [`notes/latex/chapters/sections/21.3.tex`](../../../notes/latex/chapters/sections/21.3.tex) (L290–369)  
**Audit Reference:** [`docs/plans/v1-s9/v1_release_readiness_audit.md`](../../plans/v1-s9/v1_release_readiness_audit.md)  
**Phase Status:** Phase B Complete — Awaiting Human Phase C Promotion (`lake env lean -DwarningAsError=true BosonizeStubs/Ch21CocycleAndLeakage.lean` exits `0` with zero warnings and zero `sorry`s; `python3 scripts/webllm/audit_axioms.py BosonizeStubs/Ch21CocycleAndLeakage.lean` exits `0` across all `114` exported declarations [`77` exported proofs: `31` `theorem`s + `46` `lemma`s; `37` exported data/instance commands: `30` `def`s + `2` `abbrev`s + `1` `structure` + `4` `local instance`s; `0` `private lemma`s] using standard axioms `[propext, Classical.choice, Quot.sound]` only).

---

## 1. Carrier Conventions & Physical Correspondence

| Convention | Lean Realization | Mathematical Meaning |
| :--- | :--- | :--- |
| Local mode order instances | `localModeLinearOrderCh21Ext`, `localModeLTCh21Ext`, `localModeLECh21Ext`, `localModeDecidableEqCh21Ext` | Lexicographic `A05.speciesOrder h` (`L↑ < L↓ < R↑ < R↓`, then momentum `k ∈ Ch01.Band (2*h)`) matching frozen `A05`/`Ch14`. |
| $\mathbb{Z}^4$ Klein 2-cocycle | `intParitySign`, `cocycleExponent`, `epsZ4`, `chargeBasisVec` | Bilinear lower-triangular exponent $\Phi(p, q) = \sum_{i < j} p_j q_i$ and sign $\varepsilon(p, q) = (-1)^{\Phi(p, q)} \in \{1, -1\}$ (`eq:ch21-cocycle-def`, `thm:ch21-cocycle-identity`). |
| Auxiliary charge space $\mathbb{C}^{(\mathbb{Z}^4)}$ | `ChargeSpace`, `chargeKet`, `chargeInner`, `precedingParitySign`, `cocycleShift`, `chargeTranslationOp`, `precedingParityOp`, `fourKleinOp`, `fourKleinAdj`, `chargeNumberOp` | Finitely supported Hilbert space `(SpinBranch → ℤ) →₀ ℂ` carrying projective cocycle shifts `U(p) |n⟩ = ε(p, n) |n - p⟩`, unitary Klein factors $F_i = P_{<i} T_i$ (`def:ch21-four-klein`), and charge numbers $N_i$ (`prop:ch21-klein-anticommute`). |
| Finite 16-dim $\mathbb{Z}_2^4$ Clifford Klein operators | `ParityChargeSpace`, `parityBitSign`, `flipBit`, `fourKleinMod2Op`, `chargeMod2`, `chargeParityQuotient` | Parity quotient $\pi : \mathbb{C}^{(\mathbb{Z}^4)} \to \mathbb{C}^{(\mathbb{Z}_2^4)}$ intertwining unitary shifts $F_i$ with Hermitian involutions $K_i$ ($K_i^2 = I$, $K_i K_j = -K_j K_i$). |
| Off-margin counterexample ket | `offMarginChargeL`, `offMarginKetL` | Product ket $v = |\text{full}_{L\uparrow}, \text{sea}_{L\downarrow}, \text{sea}_{R\uparrow}, \text{sea}_{R\downarrow}\rangle$ with `N_{L↑} = h` (`eq:ch21-off-margin-example`), witnessing $[R^c_{L,-1}, R^s_{L,1}] v = -v \ne 0$. |
| Spinful hyperbolic Bogoliubov blocks | `SpinfulHyperbolicBlocks`, `bogoliubovDynMatrix`, `bogoliubovTransformMatrix`, `bogoliubovTransformInvMatrix`, `freeHyperbolicParams`, `freeBlockHyperbolicParams`, `equalSpeedWitness` | Independent charge `(u_c, K_c)` and spin `(u_s, K_s)` hyperbolic diagonalization reusing frozen `A07Interactions.HyperbolicParams`, `Ch17.v1Velocity`/`v2Velocity`, and `Ch18.luttingerG` (`prop:ch21-quadratic-block`, `eq:ch21-hyperbolic-parameters`, `ex:ch21-equal-speeds`). |
| Summed Umklapp operators & charge-box leakage | `umklappForwardSum`, `umklappBackwardSum` | Total outward $\sum_x \mathcal{O}_U(x)$ and inward $\sum_x \mathcal{O}_U(x)^\dagger$ Umklapp sums acting on `speciesChargeBox h K B` (`thm:ch21-u-leakage`). |

---

## 2. Exported API, Hypotheses & Verification Inventory

### Local Instances (4 exported `local instance` declarations)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `localModeLinearOrderCh21Ext` | `local instance` | `h : ℕ` | Complete (0 `sorry`) | `LinearOrder (A05.Mode (Fin 4) h) := A05.speciesOrder h`. |
| `localModeLTCh21Ext` | `local instance` | `h : ℕ` | Complete (0 `sorry`) | `LT (A05.Mode (Fin 4) h) := (A05.speciesOrder h).toLT`. |
| `localModeLECh21Ext` | `local instance` | `h : ℕ` | Complete (0 `sorry`) | `LE (A05.Mode (Fin 4) h) := (A05.speciesOrder h).toLE`. |
| `localModeDecidableEqCh21Ext` | `local instance` | `h : ℕ` | Complete (0 `sorry`) | `DecidableEq (A05.Mode (Fin 4) h) := A05.localModeDecidableEq h`. |

### Section 1: Standalone $\mathbb{Z}^4$ Klein 2-Cocycle (`thm:ch21-cocycle-identity`, `21.1.tex` L496–533)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `intParitySign` | `def` | `k : ℤ` | Complete (0 `sorry`) | Exact integer parity sign `if k % 2 = 0 then 1 else -1` representing $(-1)^k \in \{1, -1\} \subset \mathbb{Z}$. |
| `intParitySign_add` | `lemma` | `a b : ℤ` | Proved (0 `sorry`) | `intParitySign (a + b) = intParitySign a * intParitySign b`. |
| `intParitySign_neg` | `lemma` | `a : ℤ` | Proved (0 `sorry`) | `intParitySign (-a) = intParitySign a`. |
| `intParitySign_sub` | `lemma` | `a b : ℤ` | Proved (0 `sorry`) | `intParitySign (a - b) = intParitySign a * intParitySign b`. |
| `intParitySign_sq` | `lemma` | `a : ℤ` | Proved (0 `sorry`) | `intParitySign a * intParitySign a = 1`. |
| `intParitySign_zero` | `lemma` | None | Proved (0 `sorry`) | `intParitySign 0 = 1`. |
| `intParitySign_one` | `lemma` | None | Proved (0 `sorry`) | `intParitySign 1 = -1`. |
| `intParitySign_cast_complex` | `lemma` | `k : ℤ` | Proved (0 `sorry`) | `(intParitySign k : ℂ) = (-1 : ℂ) ^ k`. |
| `cocycleExponent` | `def` | `p q : SpinBranch → ℤ` | Complete (0 `sorry`) | Strictly lower-triangular bilinear exponent $\sum_{j} \sum_{i < j} p_j q_i$ (`eq:ch21-cocycle-def`). |
| `cocycleExponent_explicit` | `lemma` | `p q : SpinBranch → ℤ` | Proved (0 `sorry`) | Expanded 4-branch form `p 1 * q 0 + p 2 * (q 0 + q 1) + p 3 * (q 0 + q 1 + q 2)`. |
| `cocycleExponent_add_left`, `cocycleExponent_add_right` | `lemma` | `p₁ p₂ q` / `p q₁ q₂ : SpinBranch → ℤ` | Proved (0 `sorry`) | Biadditivity of `cocycleExponent` in left and right arguments. |
| `cocycleExponent_neg_left`, `cocycleExponent_neg_right` | `lemma` | `p q : SpinBranch → ℤ` | Proved (0 `sorry`) | Sign reversal `cocycleExponent (-p) q = -cocycleExponent p q` and right analogue. |
| `cocycleExponent_sub_right` | `lemma` | `p q₁ q₂ : SpinBranch → ℤ` | Proved (0 `sorry`) | `cocycleExponent p (q₁ - q₂) = cocycleExponent p q₁ - cocycleExponent p q₂`. |
| `cocycleExponent_zero_left`, `cocycleExponent_zero_right` | `lemma` | `q` / `p : SpinBranch → ℤ` | Proved (0 `sorry`) | Vanishing at zero charge vector. |
| `epsZ4` | `def` | `p q : SpinBranch → ℤ` | Complete (0 `sorry`) | Four-species Klein 2-cocycle `intParitySign (cocycleExponent p q)` (`eq:ch21-cocycle-def`). |
| `epsZ4_cast_complex` | `lemma` | `p q : SpinBranch → ℤ` | Proved (0 `sorry`) | `(epsZ4 p q : ℂ) = (-1 : ℂ) ^ cocycleExponent p q`. |
| `epsZ4_sq` | `lemma` | `p q : SpinBranch → ℤ` | Proved (0 `sorry`) | `epsZ4 p q * epsZ4 p q = 1`. |
| `epsZ4_zero_left`, `epsZ4_zero_right` | `lemma` | `q` / `p : SpinBranch → ℤ` | Proved (0 `sorry`) | Normalization `epsZ4 0 q = 1` and `epsZ4 p 0 = 1`. |
| `epsZ4_add_left`, `epsZ4_add_right` | `lemma` | `p₁ p₂ q` / `p q₁ q₂ : SpinBranch → ℤ` | Proved (0 `sorry`) | Multiplicative bicharacter laws in left and right arguments. |
| `epsZ4_neg_left`, `epsZ4_neg_right` | `lemma` | `p q : SpinBranch → ℤ` | Proved (0 `sorry`) | Invariance under negation `epsZ4 (-p) q = epsZ4 p q` and `epsZ4 p (-q) = epsZ4 p q`. |
| `epsZ4_sub_right` | `lemma` | `p q₁ q₂ : SpinBranch → ℤ` | Proved (0 `sorry`) | `epsZ4 p (q₁ - q₂) = epsZ4 p q₁ * epsZ4 p q₂`. |
| `epsZ4_cocycle_identity` | `theorem` | `p q t : SpinBranch → ℤ` | Proved (0 `sorry`) | Theorem `thm:ch21-cocycle-identity` (`eq:ch21-cocycle-law`): `epsZ4 p q * epsZ4 (p + q) t = epsZ4 q t * epsZ4 p (q + t)` in `ℤ`. |
| `epsZ4_complex_cocycle_identity` | `theorem` | `p q t : SpinBranch → ℤ` | Proved (0 `sorry`) | Complex-valued form `((-1 : ℂ) ^ cocycleExponent p q) * ((-1 : ℂ) ^ cocycleExponent (p + q) t) = ((-1 : ℂ) ^ cocycleExponent q t) * ((-1 : ℂ) ^ cocycleExponent p (q + t))`. |
| `chargeBasisVec` | `def` | `i : SpinBranch` | Complete (0 `sorry`) | Canonical unit basis vector $e_i \in \mathbb{Z}^4$. |
| `cocycleExponent_basis_left` | `lemma` | `i : SpinBranch, q : SpinBranch → ℤ` | Proved (0 `sorry`) | `cocycleExponent (chargeBasisVec i) q = ∑ j ∈ Finset.univ.filter (· < i), q j`. |
| `cocycleExponent_basis_pair` | `lemma` | `i j : SpinBranch` | Proved (0 `sorry`) | `cocycleExponent (chargeBasisVec i) (chargeBasisVec j) = if j < i then 1 else 0`. |
| `epsZ4_basis_self` | `lemma` | `i : SpinBranch` | Proved (0 `sorry`) | `epsZ4 (chargeBasisVec i) (chargeBasisVec i) = 1`. |
| `epsZ4_basis_anticommute` | `lemma` | `i j : SpinBranch, i ≠ j` | Proved (0 `sorry`) | `epsZ4 (chargeBasisVec i) (chargeBasisVec j) = -epsZ4 (chargeBasisVec j) (chargeBasisVec i)`. |

### Section 1.1: Auxiliary Charge Space $\mathbb{C}^{(\mathbb{Z}^4)}$ & Unitary Four-Species Klein Factors (`def:ch21-four-klein`, `prop:ch21-klein-anticommute`, `21.1.tex` L534–574)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `ChargeSpace` | `abbrev` | None | Complete (0 `sorry`) | `(SpinBranch → ℤ) →₀ ℂ` ($\mathbb{C}^{(\mathbb{Z}^4)}$). |
| `chargeKet` | `def` | `n : SpinBranch → ℤ` | Complete (0 `sorry`) | Basis ket `Finsupp.single n 1 : ChargeSpace`. |
| `chargeInner` | `def` | `u v : ChargeSpace` | Complete (0 `sorry`) | Sesquilinear inner product `u.sum (fun n c => star c * v n)`. |
| `precedingParitySign` | `def` | `i : SpinBranch, n : SpinBranch → ℤ` | Complete (0 `sorry`) | Preceding-species parity sign $P_{<i}(n) = \prod_{j < i} (-1)^{n_j}$ (`eq:ch21-preceding-parity`). |
| `precedingParitySign_eq_epsZ4` | `lemma` | `i : SpinBranch, n : SpinBranch → ℤ` | Proved (0 `sorry`) | `precedingParitySign i n = epsZ4 (chargeBasisVec i) n`. |
| `cocycleShift` | `def` | `p : SpinBranch → ℤ` | Complete (0 `sorry`) | Projective translation `U(p) |n⟩ = ε(p, n) |n - p⟩` on `ChargeSpace`. |
| `cocycleShift_ket` | `lemma` | `p n : SpinBranch → ℤ` | Proved (0 `sorry`) | `cocycleShift p (chargeKet n) = (epsZ4 p n : ℂ) • chargeKet (n - p)`. |
| `cocycleShift_mul` | `theorem` | `p q : SpinBranch → ℤ` | Proved (0 `sorry`) | Projective representation `cocycleShift p * cocycleShift q = (epsZ4 p q : ℂ) • cocycleShift (p + q)`. |
| `cocycleShift_zero` | `lemma` | None | Proved (0 `sorry`) | `cocycleShift 0 = 1`. |
| `chargeTranslationOp` | `def` | `i : SpinBranch` | Complete (0 `sorry`) | Unitary shift $T_i |n⟩ = |n - e_i⟩$ (`def:ch21-four-klein`). |
| `precedingParityOp` | `def` | `i : SpinBranch` | Complete (0 `sorry`) | Preceding-parity operator $P_{<i} |n⟩ = P_{<i}(n) |n⟩$ (`eq:ch21-preceding-parity`). |
| `fourKleinOp` | `def` | `i : SpinBranch` | Complete (0 `sorry`) | Four-species Klein operator $F_i := P_{<i} T_i$ (`def:ch21-four-klein`, `eq:ch21-four-klein-def`). |
| `fourKleinAdj` | `def` | `i : SpinBranch` | Complete (0 `sorry`) | Adjoint Klein operator `cocycleShift (-chargeBasisVec i)`. |
| `chargeNumberOp` | `def` | `i : SpinBranch` | Complete (0 `sorry`) | Species charge number operator $N_i |n⟩ = n_i |n⟩$. |
| `fourKleinOp_ket` | `lemma` | `i : SpinBranch, n : SpinBranch → ℤ` | Proved (0 `sorry`) | `fourKleinOp i (chargeKet n) = (precedingParitySign i n : ℂ) • chargeKet (n - chargeBasisVec i)`. |
| `fourKleinOp_eq_cocycleShift` | `lemma` | `i : SpinBranch` | Proved (0 `sorry`) | `fourKleinOp i = cocycleShift (chargeBasisVec i)`. |
| `fourKleinAdj_ket` | `lemma` | `i : SpinBranch, n : SpinBranch → ℤ` | Proved (0 `sorry`) | `fourKleinAdj i (chargeKet n) = (precedingParitySign i n : ℂ) • chargeKet (n + chargeBasisVec i)`. |
| `fourKleinAdj_is_adjoint` | `lemma` | `i : SpinBranch, u v : ChargeSpace` | Proved (0 `sorry`) | `chargeInner u (fourKleinOp i v) = chargeInner (fourKleinAdj i u) v`. |
| `fourKleinOp_unitary_left` | `theorem` | `i : SpinBranch` | Proved (0 `sorry`) | Unitarity `fourKleinAdj i * fourKleinOp i = 1` ($F_i^\dagger F_i = I$). |
| `fourKleinOp_unitary_right` | `theorem` | `i : SpinBranch` | Proved (0 `sorry`) | Unitarity `fourKleinOp i * fourKleinAdj i = 1` ($F_i F_i^\dagger = I$). |
| `fourKleinOp_anticommute` | `theorem` | `i j : SpinBranch, i ≠ j` | Proved (0 `sorry`) | Proposition `prop:ch21-klein-anticommute` (1): $F_i F_j = -F_j F_i$ for $i \ne j$. |
| `fourKleinOp_anticommutator_zero` | `theorem` | `i j : SpinBranch, i ≠ j` | Proved (0 `sorry`) | Anticommutator $\{F_i, F_j\} = 0$ for $i \ne j$ (`eq:ch21-klein-anticomm-relations`). |
| `fourKleinOp_adj_anticommute` | `theorem` | `i j : SpinBranch, i ≠ j` | Proved (0 `sorry`) | Proposition `prop:ch21-klein-anticommute` (2): $F_i F_j^\dagger = -F_j^\dagger F_i$ for $i \ne j$. |
| `fourKleinOp_adj_anticommutator_zero` | `theorem` | `i j : SpinBranch, i ≠ j` | Proved (0 `sorry`) | Anticommutator $\{F_i, F_j^\dagger\} = 0$ for $i \ne j$ (`eq:ch21-klein-anticomm-relations`). |
| `fourKleinOp_number_commutator` | `theorem` | `i j : SpinBranch` | Proved (0 `sorry`) | Proposition `prop:ch21-klein-anticommute` (3): `[N_i, F_j] = -\delta_{ij} F_j` (`eq:ch21-klein-anticomm-relations`). |

### Section 1.2: Finite $\mathbb{Z}_2^4$ Clifford/Majorana Klein Operators & Parity Quotient

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `ParityChargeSpace` | `abbrev` | None | Complete (0 `sorry`) | Finite 16-dimensional parity charge space `(SpinBranch → Bool) → ℂ` ($\mathbb{C}^{(\mathbb{Z}_2^4)}$). |
| `parityBitSign` | `def` | `i : SpinBranch, b : SpinBranch → Bool` | Complete (0 `sorry`) | Preceding-bit parity sign $\prod_{j < i} (-1)^{b_j} \in \{1, -1\} \subset \mathbb{C}$. |
| `flipBit` | `def` | `i : SpinBranch, b : SpinBranch → Bool` | Complete (0 `sorry`) | `Function.update b i (!(b i))`. |
| `flipBit_involutive` | `lemma` | `i : SpinBranch, b : SpinBranch → Bool` | Proved (0 `sorry`) | `flipBit i (flipBit i b) = b`. |
| `flipBit_comm` | `lemma` | `i j : SpinBranch, i ≠ j, b` | Proved (0 `sorry`) | `flipBit i (flipBit j b) = flipBit j (flipBit i b)`. |
| `parityBitSign_flipBit` | `lemma` | `i j : SpinBranch, b` | Proved (0 `sorry`) | `parityBitSign i (flipBit j b) = if j < i then -parityBitSign i b else parityBitSign i b`. |
| `fourKleinMod2Op` | `def` | `i : SpinBranch` | Complete (0 `sorry`) | Clifford/Majorana involution `(K_i f)(b) = parityBitSign i b * f (flipBit i b)`. |
| `fourKleinMod2Op_sq` | `theorem` | `i : SpinBranch` | Proved (0 `sorry`) | Involution `fourKleinMod2Op i * fourKleinMod2Op i = 1` ($K_i^2 = I$). |
| `fourKleinMod2Op_anticommute` | `theorem` | `i j : SpinBranch, i ≠ j` | Proved (0 `sorry`) | Mutual anticommutation `fourKleinMod2Op i * fourKleinMod2Op j = -(fourKleinMod2Op j * fourKleinMod2Op i)`. |
| `chargeMod2` | `def` | `n : SpinBranch → ℤ` | Complete (0 `sorry`) | Parity quotient $\pi : \mathbb{Z}^4 \to \mathbb{Z}_2^4$ (`fun ν => decide (n ν % 2 ≠ 0)`). |
| `chargeParityQuotient` | `def` | None | Complete (0 `sorry`) | Linear map `ChargeSpace →ₗ[ℂ] ParityChargeSpace` sending `|n⟩ ↦ δ_{chargeMod2 n}`. |
| `chargeParityQuotient_intertwines` | `theorem` | `i : SpinBranch` | Proved (0 `sorry`) | Intertwining `chargeParityQuotient ∘ₗ fourKleinOp i = fourKleinMod2Op i ∘ₗ chargeParityQuotient` ($\pi \circ F_i = K_i \circ \pi$). |

### Section 2: First-Mode Oscillator & Off-Margin Counterexample (`ex:ch21-first-mode`, `eq:ch21-off-margin-example`, `eq:ch21-compression-residual`, `21.1.tex` L340–401)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `first_mode_charge_spin_commutators` | `theorem` | `h : ℕ, 2 ≤ h` | Proved (0 `sorry`) | `ex:ch21-first-mode` (`eq:ch21-example-two`): on `Ω₀`, `[R^c_{L,-1}, R^c_{L,1}] Ω₀ = 2 Ω₀`, `[R^s_{L,-1}, R^s_{L,1}] Ω₀ = 2 Ω₀`, and `[R^c_{L,-1}, R^s_{L,1}] Ω₀ = 0`. |
| `first_mode_charge_spin_commutators_h2` | `theorem` | None | Proved (0 `sorry`) | Concrete `h = 2` specialization of `first_mode_charge_spin_commutators`. |
| `offMarginChargeL` | `def` | `h : ℕ, ν : SpinBranch` | Complete (0 `sorry`) | Charge vector `(h, 0, 0, 0)` (filled `L↑` band, sea ground on `L↓, R↑, R↓`). |
| `offMarginChargeL_admissible` | `lemma` | `h : ℕ` | Proved (0 `sorry`) | `A05.admissible h (offMarginChargeL h)`. |
| `offMarginKetL` | `def` | `h : ℕ` | Complete (0 `sorry`) | `A05.groundKet h (offMarginChargeL h)` (`eq:ch21-off-margin-example`). |
| `offMarginKetL_ne_zero` | `lemma` | `h : ℕ` | Proved (0 `sorry`) | `offMarginKetL h ≠ 0`. |
| `rho_full_band_annihilates` | `lemma` | `h : ℕ, m : ℤ, m ≠ 0` | Proved (0 `sorry`) | `A05.rho h brLUp m (offMarginKetL h) = 0` via Pauli blocking on the filled `L↑` band. |
| `off_margin_commutator_counterexample` | `theorem` | `h : ℕ, 2 ≤ h` | Proved (0 `sorry`) | Equation `eq:ch21-off-margin-example`: `[R^c_{L,-1}, R^s_{L,1}] (offMarginKetL h) = -(offMarginKetL h)` for all `h ≥ 2`. |
| `off_margin_commutator_counterexample_h2` | `theorem` | None | Proved (0 `sorry`) | Concrete `h = 2` witness `[R^c_{L,-1}, R^s_{L,1}] v = -v ∧ [R^c_{L,-1}, R^s_{L,1}] v ≠ 0`. |
| `rhoChargeL_rhoSpinL_global_ne_zero` | `theorem` | `h : ℕ, 2 ≤ h` | Proved (0 `sorry`) | Unrestricted global non-commutativity `[R^c_{L,-1}, R^s_{L,1}] ≠ 0` for every `h ≥ 2`. |
| `compressed_commutator_residual` | `theorem` | `[AddCommGroup V] [Module ℂ V], P A B : Module.End ℂ V, P * P = P` | Proved (0 `sorry`) | Equation `eq:ch21-compression-residual`: `[P A P, P B P] = P [A, B] P - P A (1 - P) B P + P B (1 - P) A P`. |

### Section 3: Spinful Charge/Spin Hyperbolic Quadratic Block Diagonalization (`prop:ch21-quadratic-block`, `eq:ch21-hyperbolic-parameters`, `ex:ch21-equal-speeds`, `21.1.tex` L633–802)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `ordered_quadratic_block_diagonalization` | `theorem` | `[Ring R] [Algebra ℂ R], a b : ℂ, XUp XDown YUp YDown : R` | Proved (0 `sorry`) | Proposition `prop:ch21-quadratic-block` (`eq:ch21-quadratic-block`): ordered noncommutative identity `a(X_↑ Y_↑ + X_↓ Y_↓) + b(X_↑ Y_↓ + X_↓ Y_↑) = ((a+b)/2) X_c Y_c + ((a-b)/2) X_s Y_s`. |
| `asymmetric_quadratic_mixes_charge_spin` | `theorem` | `[Ring R] [Algebra ℂ R], aUp aDown : ℂ, XUp XDown YUp YDown : R` | Proved (0 `sorry`) | Equation `eq:ch21-asymmetry-mixes`: `a_↑ X_↑ Y_↑ + a_↓ X_↓ Y_↓ = ((a_↑+a_↓)/4)(X_c Y_c + X_s Y_s) + ((a_↑-a_↓)/4)(X_c Y_s + X_s Y_c)`. |
| `spinful_block_stability_iff` | `lemma` | `vF g4 g2 : ℝ` | Proved (0 `sorry`) | `|g2| < 2π v_F + g4 ↔ |Ch17.v2Velocity g2| < Ch17.v1Velocity vF g4`. |
| `SpinfulHyperbolicBlocks` | `structure` | `vF g4c g2c g4s g2s : ℝ` | Complete (0 `sorry`) | Pair of independent `A07Interactions.HyperbolicParams` (`charge` and `spin`) (`eq:ch21-hyperbolic-parameters`). |
| `SpinfulHyperbolicBlocks.Kc` | `def` | `B : SpinfulHyperbolicBlocks vF g4c g2c g4s g2s` | Complete (0 `sorry`) | Charge Luttinger parameter $K_c = (c_c - s_c)^2$ via `Ch18.luttingerG`. |
| `SpinfulHyperbolicBlocks.Ks` | `def` | `B : SpinfulHyperbolicBlocks vF g4c g2c g4s g2s` | Complete (0 `sorry`) | Spin Luttinger parameter $K_s = (c_s - s_s)^2$ via `Ch18.luttingerG`. |
| `spinful_hyperbolic_blocks_nonempty` | `theorem` | `|g2c| < 2π vF + g4c`, `|g2s| < 2π vF + g4s` | Proved (0 `sorry`) | Existence `Nonempty (SpinfulHyperbolicBlocks vF g4c g2c g4s g2s)` under independent stability inequalities. |
| `bogoliubovDynMatrix` | `def` | `v1 v2 : ℝ` | Complete (0 `sorry`) | `2×2` dynamical matrix `!![v1, v2; -v2, -v1]` (`eq:ch21-bogoliubov-dynamic`). |
| `bogoliubovTransformMatrix` | `def` | `c s : ℝ` | Complete (0 `sorry`) | Hyperbolic squeezing matrix `!![c, s; s, c]`. |
| `bogoliubovTransformInvMatrix` | `def` | `c s : ℝ` | Complete (0 `sorry`) | Inverse hyperbolic matrix `!![c, -s; -s, c]`. |
| `bogoliubov_block_diagonalizes` | `theorem` | `hp : A07Interactions.HyperbolicParams v1 v2` | Proved (0 `sorry`) | Exact inverse identities `B * B⁻¹ = 1`, `B⁻¹ * B = 1`, and `B * M(v1, v2) * B⁻¹ = !![hp.u, 0; 0, -hp.u]`. |
| `spinful_charge_spin_diagonalization` | `theorem` | `B : SpinfulHyperbolicBlocks vF g4c g2c g4s g2s` | Proved (0 `sorry`) | Simultaneous `2×2` Bogoliubov diagonalization of charge `(u_c, K_c)` and spin `(u_s, K_s)` blocks plus exact square-root formulas `eq:ch21-block-speed` and `eq:ch21-hyperbolic-parameters`. |
| `spinful_speed_nondegeneracy_iff` | `theorem` | `hc : HyperbolicParams v1c v2c`, `hs : HyperbolicParams v1s v2s` | Proved (0 `sorry`) | Equation `eq:ch21-speed-nondegeneracy`: `hc.u ≠ hs.u ↔ v1c^2 - v2c^2 ≠ v1s^2 - v2s^2`. |
| `freeHyperbolicParams` | `def` | `v : ℝ, 0 < v` | Complete (0 `sorry`) | Explicit `A07Interactions.HyperbolicParams v 0` with `(u, c, s) = (v, 1, 0)`. |
| `freeBlockHyperbolicParams` | `def` | `v : ℝ, 0 < v` | Complete (0 `sorry`) | Explicit `HyperbolicParams (Ch17.v1Velocity v 0) (Ch17.v2Velocity 0)`. |
| `equalSpeedWitness` | `def` | `v : ℝ, 0 < v` | Complete (0 `sorry`) | `SpinfulHyperbolicBlocks v 0 0 0 0` (`ex:ch21-equal-speeds`). |
| `equal_speed_witness_degenerate` | `theorem` | `v : ℝ, 0 < v` | Proved (0 `sorry`) | `ex:ch21-equal-speeds`: proves `u_c = v`, `u_s = v`, `u_c = u_s`, `K_c = 1`, and `K_s = 1`. |
| `distinct_speed_contrast_witness` | `theorem` | None | Proved (0 `sorry`) | Contrast witness from `ex:ch21-equal-speeds`: `hc.u = 8`, `hs.u = 5`, `hc.u ≠ hs.u`, `K_c = 1/4`, `K_s = 1`. |

### Section 4: General Per-Species Charge-Box Outward & Inward Leakage (`thm:ch21-u-leakage`, `21.3.tex` L290–369)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `umklappForwardSum` | `def` | `h : ℕ, b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)` | Complete (0 `sorry`) | Summed outward Umklapp operator $\sum_{x \in \Lambda_L} \mathcal{O}_U(x)$. |
| `umklappBackwardSum` | `def` | `h : ℕ, b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)` | Complete (0 `sorry`) | Summed inward Umklapp operator $\sum_{x \in \Lambda_L} \mathcal{O}_U(x)^\dagger$. |
| `umklappOp_eq_smul_add_sums` | `lemma` | `h : ℕ, b, gU : ℝ` | Proved (0 `sorry`) | `umklappOp h b gU = ((gU : ℂ) / (2 * (h : ℂ))) • (umklappForwardSum h b + umklappBackwardSum h b)`. |
| `umklappForwardSum_maps_sector` | `lemma` | `ψ ∈ chargeSector h Ns` | Proved (0 `sorry`) | `umklappForwardSum h b ψ ∈ chargeSector h (umklappForwardTarget Ns)`. |
| `umklappBackwardSum_maps_sector` | `lemma` | `ψ ∈ chargeSector h Ns` | Proved (0 `sorry`) | `umklappBackwardSum h b ψ ∈ chargeSector h (umklappBackwardTarget Ns)`. |
| `chargeSector_orthogonal_speciesChargeBox` | `lemma` | `∃ ν, (B ν : ℤ) < \|T ν\|`, `u ∈ chargeSector h T`, `w ∈ speciesChargeBox h K B` | Proved (0 `sorry`) | Exact orthogonality `inner ℂ u w = 0` for any charge sector violating a box bound `B_ν`. |
| `umklapp_charge_box_outward_leakage` | `theorem` | `0 < h`, `gU ≠ 0`, `ψ ∈ speciesChargeBox h K B`, `ψ ∈ chargeSector h Ns`, `umklappForwardSum h b ψ ≠ 0`, `∃ ν, (B ν : ℤ) < \|umklappForwardTarget Ns ν\|` | Proved (0 `sorry`) | Theorem `thm:ch21-u-leakage` (`eq:ch21-u-leakage-hypotheses`, `eq:ch21-u-projector-noncommute`, `eq:ch21-u-projected-outward`, outward branch): proves `H_U ψ ∉ ℬ_{K,B}`, `[P_{K,B}, H_U] ψ ≠ 0`, and `[P_{K,B}, H_U] ≠ 0`. |
| `umklapp_charge_box_inward_leakage` | `theorem` | `0 < h`, `gU ≠ 0`, `ψ ∈ speciesChargeBox h K B`, `ψ ∈ chargeSector h Ns`, `umklappBackwardSum h b ψ ≠ 0`, `∃ ν, (B ν : ℤ) < \|umklappBackwardTarget Ns ν\|` | Proved (0 `sorry`) | Theorem `thm:ch21-u-leakage` (inward / adjoint branch): symmetric leakage `H_U ψ ∉ ℬ_{K,B}`, `[P_{K,B}, H_U] ψ ≠ 0`, and `[P_{K,B}, H_U] ≠ 0`. |
| `umklapp_charge_box_basis_leakage` | `theorem` | `0 < h`, `gU ≠ 0`, `S ∈ speciesChargeBoxSet h K B`, nonzero outward or inward step exiting `±B_ν` | Proved (0 `sorry`) | Basis-ket corollary yielding `[speciesChargeBoxProjection h K B, umklappOp h b gU] ≠ 0`. |
| `umklapp_zero_box_commutator_ne_zero` | `theorem` | `0 < h`, `gU ≠ 0` | Proved (0 `sorry`) | Immediate zero-box corollary `[speciesChargeBoxProjection h K (fun _ => 0), periodicUmklappOp h gU] ≠ 0`. |

---

## 3. Verification Summary

- `lake env lean -DwarningAsError=true BosonizeStubs/Ch21CocycleAndLeakage.lean`: exit `0` (zero warnings, zero errors, zero `sorry`s).
- `python3 scripts/webllm/audit_axioms.py BosonizeStubs/Ch21CocycleAndLeakage.lean`: exit `0` (`114` exported declarations, standard axioms `[propext, Classical.choice, Quot.sound]` only).
- `python3 scripts/guards/core_lock.py`: exit `0` (`44` Core files untouched).
- `python3 -m unittest discover -s scripts/guards -p 'test_*.py'`: exit `0` (`69` tests).
- `python3 scripts/check_book_sources.py`: exit `0`.
- `python3 /home/lu/Projects/scripts/uow.py check --repo bosonize-lean`: exit `0`.
