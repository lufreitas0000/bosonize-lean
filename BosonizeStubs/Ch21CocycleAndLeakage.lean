import BosonizeStubs.Ch21SpinfulModels

/-!
# Chapter 21 Extensions: Z⁴ Klein 2-Cocycle, Off-Margin Counterexample, Spinful Hyperbolic Diagonalization, and General Charge-Box Umklapp Leakage

Constructive Phase B formalization closing the remaining algebraic and finite-CAR claims of
Chapter 21 (`notes/latex/chapters/sections/21.1.tex` and `21.3.tex`) on top of
`BosonizeStubs.Ch21SpinfulModels` and frozen Core (`Bosonize.Core.*`):

1. **Standalone `ℤ⁴` Klein 2-Cocycle & Four-Species Anticommuting Operators**
   (`thm:ch21-cocycle-identity`, `def:ch21-four-klein`, `prop:ch21-klein-anticommute`):
   - Bilinear triangular sign `epsZ4 (p q : SpinBranch → ℤ) : ℤ` representing
     `(-1)^(∑_{i < j} p_j q_i)`, exact 2-cocycle identity
     `epsZ4 p q * epsZ4 (p + q) t = epsZ4 q t * epsZ4 p (q + t)` for all `p, q, t : Fin 4 → ℤ`,
     and complex-valued bridge `(-1 : ℂ) ^ cocycleExponent p q`.
   - Auxiliary charge space `ChargeSpace := (SpinBranch → ℤ) →₀ ℂ` (`ℂ^(ℤ⁴)`), unitary shift
     operators `T_i`, preceding-parity operators `P_{<i}`, four-species Klein factors
     `fourKleinOp i := P_{<i} T_i`, adjoints `fourKleinAdj i`, cocycle shift representation
     `cocycleShift p * cocycleShift q = epsZ4(p, q) • cocycleShift (p + q)`, unitarity
     `F_i† F_i = F_i F_i† = I`, mutual anticommutation `{F_i, F_j} = 0` and `{F_i, F_j†} = 0`
     for `i ≠ j`, and number-shift commutator `[N_i, F_j] = -δ_{ij} F_j`.
   - Finite 16-dimensional `ℤ₂⁴` Clifford/Majorana Klein operators `fourKleinMod2Op` satisfying
     exact involution `K_i² = I` and mutual anticommutation `K_i K_j = -K_j K_i` (`i ≠ j`),
     intertwined with `fourKleinOp` via the parity quotient map.

2. **First-Mode Oscillator & Off-Margin Commutator Counterexample**
   (`ex:ch21-first-mode`, `eq:ch21-off-margin-example`, `eq:ch21-compression-residual`):
   - Explicit `h ≥ 2` (and `h = 2`) first-mode evaluations `[R^c_{L,-1}, R^c_{L,1}] Ω = 2 Ω`,
     `[R^s_{L,-1}, R^s_{L,1}] Ω = 2 Ω`, `[R^c_{L,-1}, R^s_{L,1}] Ω = 0`.
   - Explicit off-margin counterexample ket `offMarginKetL h` (full up-spin band `N_{L↑} = h`,
     sea ground on `L↓, R↑, R↓`) for every `h ≥ 2` (specialized to `h = 2`), proving
     `[R^c_{L,-1}, R^s_{L,1}] v = -v ≠ 0` and global non-commutativity `[R^c_{L,-1}, R^s_{L,1}] ≠ 0`,
     plus the exact compression-residual identity `[P A P, P B P] = P [A, B] P - P A Q B P + P B Q A P`.

3. **Spinful Charge/Spin Hyperbolic Quadratic Block Diagonalization**
   (`prop:ch21-quadratic-block`, `eq:ch21-asymmetry-mixes`, `eq:ch21-bogoliubov-dynamic`,
   `eq:ch21-hyperbolic-parameters`, `ex:ch21-equal-speeds`):
   - Ordered noncommutative quadratic block diagonalization
     `a(X_↑ Y_↑ + X_↓ Y_↓) + b(X_↑ Y_↓ + X_↓ Y_↑) = ((a+b)/2) X_c Y_c + ((a-b)/2) X_s Y_s`
     and asymmetric spin-mixing identity (`eq:ch21-asymmetry-mixes`).
   - Independent charge `(u_c, K_c)` and spin `(u_s, K_s)` hyperbolic diagonalization reusing
     `Ch17.v1Velocity`, `Ch17.v2Velocity`, `A07Interactions.HyperbolicParams`,
     `A07Interactions.hyperbolic_params_exist`, and `Ch18.luttingerG` under
     `|g_{2,c}| < 2π v_F + g_{4,c}` and `|g_{2,s}| < 2π v_F + g_{4,s}`, including explicit `2×2`
     Bogoliubov dynamical-matrix diagonalization `B M B⁻¹ = diag(u, -u)`, speed non-degeneracy
     equivalence `u_c ≠ u_s ↔ v_{1,c}² - v_{2,c}² ≠ v_{1,s}² - v_{2,s}²`, equal-speed degeneracy
     witness (`u_c = u_s = v`), and distinct-speed contrast witness (`u_c = 8 ≠ 5 = u_s`).

4. **General Per-Species Charge-Box Outward & Inward Leakage** (`thm:ch21-u-leakage`):
   - Using `speciesChargeBox` and `speciesChargeBoxProjection` from `Ch21SpinfulModels.lean`,
     proves that for arbitrary `h > 0`, `K`, `B`, boundary twist `b`, `g_U ≠ 0`, and definite-charge
     state `ψ ∈ ℬ_{K,B}` (including basis kets `|S⟩`), whenever the summed outward (or inward)
     Umklapp action is nonzero and its shifted charge vector exits a species bound `B_ν`,
     `H_U ψ ∉ ℬ_{K,B}` and `[P_{K,B}, H_U] ≠ 0`.
-/

namespace Bosonize.Ch21

open scoped BigOperators ComplexConjugate

noncomputable local instance localModeLinearOrderCh21Ext (h : ℕ) :
    LinearOrder (A05.Mode (Fin 4) h) := A05.speciesOrder h
noncomputable local instance localModeLTCh21Ext (h : ℕ) :
    LT (A05.Mode (Fin 4) h) := (A05.speciesOrder h).toLT
noncomputable local instance localModeLECh21Ext (h : ℕ) :
    LE (A05.Mode (Fin 4) h) := (A05.speciesOrder h).toLE
noncomputable local instance localModeDecidableEqCh21Ext (h : ℕ) :
    DecidableEq (A05.Mode (Fin 4) h) := A05.localModeDecidableEq h

/-! ## 1. Standalone `ℤ⁴` Klein 2-Cocycle & Four-Species Anticommuting Operators -/

/-- Exact integer parity sign `(-1)^k ∈ {1, -1}` in `ℤ`. -/
def intParitySign (k : ℤ) : ℤ :=
  if k % 2 = 0 then 1 else -1

lemma intParitySign_add (a b : ℤ) :
    intParitySign (a + b) = intParitySign a * intParitySign b := by
  unfold intParitySign
  have ha : a % 2 = 0 ∨ a % 2 = 1 := Int.emod_two_eq_zero_or_one a
  have hb : b % 2 = 0 ∨ b % 2 = 1 := Int.emod_two_eq_zero_or_one b
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [Int.add_emod, ha, hb]

lemma intParitySign_neg (a : ℤ) :
    intParitySign (-a) = intParitySign a := by
  unfold intParitySign
  have ha : a % 2 = 0 ∨ a % 2 = 1 := Int.emod_two_eq_zero_or_one a
  rcases ha with ha | ha
  · have hneg : (-a) % 2 = 0 := by omega
    simp [ha, hneg]
  · have hneg : (-a) % 2 = 1 := by omega
    simp [ha, hneg]

lemma intParitySign_sub (a b : ℤ) :
    intParitySign (a - b) = intParitySign a * intParitySign b := by
  rw [sub_eq_add_neg, intParitySign_add, intParitySign_neg]

lemma intParitySign_sq (a : ℤ) :
    intParitySign a * intParitySign a = 1 := by
  unfold intParitySign
  split_ifs <;> norm_num

lemma intParitySign_zero : intParitySign 0 = 1 := by
  simp [intParitySign]

lemma intParitySign_one : intParitySign 1 = -1 := by
  simp [intParitySign]

lemma intParitySign_cast_complex (k : ℤ) :
    (intParitySign k : ℂ) = (-1 : ℂ) ^ k := by
  unfold intParitySign
  have hk : k % 2 = 0 ∨ k % 2 = 1 := Int.emod_two_eq_zero_or_one k
  rcases hk with h0 | h1
  · simp only [h0, ↓reduceIte, Int.cast_one]
    have hdiv : k = 2 * (k / 2) := by omega
    rw [hdiv, zpow_mul]
    norm_num
  · simp only [h1, one_ne_zero, ↓reduceIte, Int.cast_neg, Int.cast_one]
    have hdiv : k = 2 * (k / 2) + 1 := by omega
    rw [hdiv, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]
    norm_num

/-- Strictly lower-triangular bilinear exponent `∑_{i < j} p_j q_i` on `ℤ⁴` (`eq:ch21-cocycle-def`). -/
def cocycleExponent (p q : SpinBranch → ℤ) : ℤ :=
  ∑ j : SpinBranch, ∑ i ∈ Finset.univ.filter (· < j), p j * q i

lemma cocycleExponent_explicit (p q : SpinBranch → ℤ) :
    cocycleExponent p q =
      p 1 * q 0 + p 2 * (q 0 + q 1) + p 3 * (q 0 + q 1 + q 2) := by
  unfold cocycleExponent
  rw [Fin.sum_univ_four]
  have h0 : (Finset.univ.filter (· < (0 : SpinBranch)) : Finset SpinBranch) = ∅ := by decide
  have h1 : (Finset.univ.filter (· < (1 : SpinBranch)) : Finset SpinBranch) = {0} := by decide
  have h2 : (Finset.univ.filter (· < (2 : SpinBranch)) : Finset SpinBranch) = {0, 1} := by decide
  have h3 : (Finset.univ.filter (· < (3 : SpinBranch)) : Finset SpinBranch) = {0, 1, 2} := by decide
  rw [h0, h1, h2, h3]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert (by decide : (0 : SpinBranch) ∉ ({1} : Finset SpinBranch)),
    Finset.sum_insert (by decide : (0 : SpinBranch) ∉ ({1, 2} : Finset SpinBranch)),
    Finset.sum_insert (by decide : (1 : SpinBranch) ∉ ({2} : Finset SpinBranch))]
  ring

lemma cocycleExponent_add_left (p₁ p₂ q : SpinBranch → ℤ) :
    cocycleExponent (p₁ + p₂) q = cocycleExponent p₁ q + cocycleExponent p₂ q := by
  simp only [cocycleExponent_explicit, Pi.add_apply]
  ring

lemma cocycleExponent_add_right (p q₁ q₂ : SpinBranch → ℤ) :
    cocycleExponent p (q₁ + q₂) = cocycleExponent p q₁ + cocycleExponent p q₂ := by
  simp only [cocycleExponent_explicit, Pi.add_apply]
  ring

lemma cocycleExponent_neg_left (p q : SpinBranch → ℤ) :
    cocycleExponent (-p) q = -cocycleExponent p q := by
  simp only [cocycleExponent_explicit, Pi.neg_apply]
  ring

lemma cocycleExponent_neg_right (p q : SpinBranch → ℤ) :
    cocycleExponent p (-q) = -cocycleExponent p q := by
  simp only [cocycleExponent_explicit, Pi.neg_apply]
  ring

lemma cocycleExponent_sub_right (p q₁ q₂ : SpinBranch → ℤ) :
    cocycleExponent p (q₁ - q₂) = cocycleExponent p q₁ - cocycleExponent p q₂ := by
  simp only [cocycleExponent_explicit, Pi.sub_apply]
  ring

lemma cocycleExponent_zero_left (q : SpinBranch → ℤ) : cocycleExponent 0 q = 0 := by
  simp [cocycleExponent_explicit]

lemma cocycleExponent_zero_right (p : SpinBranch → ℤ) : cocycleExponent p 0 = 0 := by
  simp [cocycleExponent_explicit]

/-- Four-species Klein 2-cocycle `ε(p, q) = (-1)^(∑_{i < j} p_j q_i) ∈ {±1}` (`eq:ch21-cocycle-def`). -/
def epsZ4 (p q : SpinBranch → ℤ) : ℤ :=
  intParitySign (cocycleExponent p q)

lemma epsZ4_cast_complex (p q : SpinBranch → ℤ) :
    (epsZ4 p q : ℂ) = (-1 : ℂ) ^ cocycleExponent p q :=
  intParitySign_cast_complex (cocycleExponent p q)

lemma epsZ4_sq (p q : SpinBranch → ℤ) : epsZ4 p q * epsZ4 p q = 1 :=
  intParitySign_sq (cocycleExponent p q)

lemma epsZ4_zero_left (q : SpinBranch → ℤ) : epsZ4 0 q = 1 := by
  simp [epsZ4, cocycleExponent_zero_left, intParitySign_zero]

lemma epsZ4_zero_right (p : SpinBranch → ℤ) : epsZ4 p 0 = 1 := by
  simp [epsZ4, cocycleExponent_zero_right, intParitySign_zero]

lemma epsZ4_add_left (p₁ p₂ q : SpinBranch → ℤ) :
    epsZ4 (p₁ + p₂) q = epsZ4 p₁ q * epsZ4 p₂ q := by
  unfold epsZ4
  rw [cocycleExponent_add_left, intParitySign_add]

lemma epsZ4_add_right (p q₁ q₂ : SpinBranch → ℤ) :
    epsZ4 p (q₁ + q₂) = epsZ4 p q₁ * epsZ4 p q₂ := by
  unfold epsZ4
  rw [cocycleExponent_add_right, intParitySign_add]

lemma epsZ4_neg_left (p q : SpinBranch → ℤ) : epsZ4 (-p) q = epsZ4 p q := by
  unfold epsZ4
  rw [cocycleExponent_neg_left, intParitySign_neg]

lemma epsZ4_neg_right (p q : SpinBranch → ℤ) : epsZ4 p (-q) = epsZ4 p q := by
  unfold epsZ4
  rw [cocycleExponent_neg_right, intParitySign_neg]

lemma epsZ4_sub_right (p q₁ q₂ : SpinBranch → ℤ) :
    epsZ4 p (q₁ - q₂) = epsZ4 p q₁ * epsZ4 p q₂ := by
  unfold epsZ4
  rw [cocycleExponent_sub_right, intParitySign_sub]

/-- Theorem `thm:ch21-cocycle-identity`: exact group 2-cocycle law on `ℤ⁴` in `ℤ`. -/
theorem epsZ4_cocycle_identity (p q t : SpinBranch → ℤ) :
    epsZ4 p q * epsZ4 (p + q) t = epsZ4 q t * epsZ4 p (q + t) := by
  unfold epsZ4
  rw [← intParitySign_add, ← intParitySign_add]
  congr 1
  simp only [cocycleExponent_explicit, Pi.add_apply]
  ring

/-- Complex-valued form of `thm:ch21-cocycle-identity` (`(-1)^Φ_L = (-1)^Φ_R` in `ℂ`). -/
theorem epsZ4_complex_cocycle_identity (p q t : SpinBranch → ℤ) :
    ((-1 : ℂ) ^ cocycleExponent p q) * ((-1 : ℂ) ^ cocycleExponent (p + q) t) =
      ((-1 : ℂ) ^ cocycleExponent q t) * ((-1 : ℂ) ^ cocycleExponent p (q + t)) := by
  simp only [← epsZ4_cast_complex, ← Int.cast_mul, epsZ4_cocycle_identity]

/-- Canonical unit basis vector `e_i ∈ ℤ⁴` for species `i : SpinBranch`. -/
def chargeBasisVec (i : SpinBranch) : SpinBranch → ℤ :=
  fun j => if j = i then 1 else 0

lemma cocycleExponent_basis_left (i : SpinBranch) (q : SpinBranch → ℤ) :
    cocycleExponent (chargeBasisVec i) q = ∑ j ∈ Finset.univ.filter (· < i), q j := by
  unfold cocycleExponent
  rw [Finset.sum_eq_single i]
  · simp [chargeBasisVec]
  · intro j _ hji
    simp [chargeBasisVec, hji]
  · simp

lemma cocycleExponent_basis_pair (i j : SpinBranch) :
    cocycleExponent (chargeBasisVec i) (chargeBasisVec j) = if j < i then 1 else 0 := by
  rw [cocycleExponent_basis_left]
  by_cases hlt : j < i
  · rw [Finset.sum_eq_single j]
    · simp [chargeBasisVec, hlt]
    · intro k _ hkj
      simp [chargeBasisVec, hkj]
    · intro hnot
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hlt⟩) hnot
  · rw [Finset.sum_eq_zero]
    · simp [hlt]
    · intro k hk
      have hki : k < i := (Finset.mem_filter.mp hk).2
      have hne : k ≠ j := fun he => hlt (he ▸ hki)
      simp [chargeBasisVec, hne]

lemma epsZ4_basis_self (i : SpinBranch) :
    epsZ4 (chargeBasisVec i) (chargeBasisVec i) = 1 := by
  simp [epsZ4, cocycleExponent_basis_pair, intParitySign_zero]

lemma epsZ4_basis_anticommute (i j : SpinBranch) (hne : i ≠ j) :
    epsZ4 (chargeBasisVec i) (chargeBasisVec j) =
      -epsZ4 (chargeBasisVec j) (chargeBasisVec i) := by
  unfold epsZ4
  rw [cocycleExponent_basis_pair, cocycleExponent_basis_pair]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hnot : ¬ j < i := not_lt_of_gt hlt
    simp [hlt, hnot, intParitySign_zero, intParitySign_one]
  · have hnot : ¬ i < j := not_lt_of_gt hgt
    simp [hgt, hnot, intParitySign_zero, intParitySign_one]

/-! ### 1.1 Auxiliary Charge Space `ℂ^(ℤ⁴)` and Unitary Four-Species Klein Factors (`def:ch21-four-klein`, `prop:ch21-klein-anticommute`) -/

/-- Auxiliary charge space `ℂ^(ℤ⁴)` of finitely supported amplitudes on `ℤ⁴`. -/
abbrev ChargeSpace := (SpinBranch → ℤ) →₀ ℂ

/-- Charge basis ket `|n⟩ ∈ ℂ^(ℤ⁴)`. -/
noncomputable def chargeKet (n : SpinBranch → ℤ) : ChargeSpace :=
  Finsupp.single n 1

/-- Standard sesquilinear inner product `⟨u, v⟩ = ∑_n conj(u(n)) v(n)` on `ℂ^(ℤ⁴)`. -/
noncomputable def chargeInner (u v : ChargeSpace) : ℂ :=
  u.sum (fun n c => star c * v n)

/-- Preceding-species parity sign `P_{<i}(n) = ∏_{j < i} (-1)^{n_j}` (`eq:ch21-preceding-parity`). -/
def precedingParitySign (i : SpinBranch) (n : SpinBranch → ℤ) : ℤ :=
  intParitySign (∑ j ∈ Finset.univ.filter (· < i), n j)

lemma precedingParitySign_eq_epsZ4 (i : SpinBranch) (n : SpinBranch → ℤ) :
    precedingParitySign i n = epsZ4 (chargeBasisVec i) n := by
  unfold precedingParitySign epsZ4
  rw [cocycleExponent_basis_left]

/-- Twisted cocycle translation operator `U(p) |n⟩ = ε(p, n) |n - p⟩` on `ℂ^(ℤ⁴)`. -/
noncomputable def cocycleShift (p : SpinBranch → ℤ) : Module.End ℂ ChargeSpace :=
  Finsupp.lsum ℂ (fun n => LinearMap.toSpanSingleton ℂ ChargeSpace ((epsZ4 p n : ℂ) • chargeKet (n - p)))

lemma cocycleShift_ket (p n : SpinBranch → ℤ) :
    cocycleShift p (chargeKet n) = (epsZ4 p n : ℂ) • chargeKet (n - p) := by
  simp [cocycleShift, chargeKet]

/-- Exact projective multiplication law `U(p) U(q) = ε(p, q) U(p + q)` on `ℂ^(ℤ⁴)`. -/
theorem cocycleShift_mul (p q : SpinBranch → ℤ) :
    cocycleShift p * cocycleShift q = (epsZ4 p q : ℂ) • cocycleShift (p + q) := by
  apply Finsupp.lhom_ext'
  intro n
  apply LinearMap.ext_ring
  change cocycleShift p (cocycleShift q (chargeKet n)) =
    (epsZ4 p q : ℂ) • cocycleShift (p + q) (chargeKet n)
  rw [cocycleShift_ket, map_smul, cocycleShift_ket, cocycleShift_ket, smul_smul, smul_smul]
  have hsub : n - q - p = n - (p + q) := by ext ν; simp; ring
  rw [hsub]
  congr 1
  rw [epsZ4_sub_right, epsZ4_add_left]
  push_cast
  ring

lemma cocycleShift_zero : cocycleShift 0 = 1 := by
  apply Finsupp.lhom_ext'
  intro n
  apply LinearMap.ext_ring
  change cocycleShift 0 (chargeKet n) = chargeKet n
  rw [cocycleShift_ket, epsZ4_zero_left]
  simp

/-- Unitary charge translation operator `T_i |n⟩ = |n - e_i⟩` (`def:ch21-four-klein`). -/
noncomputable def chargeTranslationOp (i : SpinBranch) : Module.End ℂ ChargeSpace :=
  Finsupp.lsum ℂ (fun n => LinearMap.toSpanSingleton ℂ ChargeSpace (chargeKet (n - chargeBasisVec i)))

/-- Preceding-parity operator `P_{<i} |n⟩ = (∏_{j < i} (-1)^{n_j}) |n⟩` (`eq:ch21-preceding-parity`). -/
noncomputable def precedingParityOp (i : SpinBranch) : Module.End ℂ ChargeSpace :=
  Finsupp.lsum ℂ (fun n => LinearMap.toSpanSingleton ℂ ChargeSpace ((precedingParitySign i n : ℂ) • chargeKet n))

/-- Four-species Klein operator `F_i := P_{<i} T_i` (`def:ch21-four-klein`, Eq. (21.29)). -/
noncomputable def fourKleinOp (i : SpinBranch) : Module.End ℂ ChargeSpace :=
  precedingParityOp i * chargeTranslationOp i

/-- Adjoint four-species Klein operator `F_i† |n⟩ = P_{<i}(n) |n + e_i⟩`. -/
noncomputable def fourKleinAdj (i : SpinBranch) : Module.End ℂ ChargeSpace :=
  cocycleShift (-chargeBasisVec i)

/-- Species charge number operator `N_i |n⟩ = n_i |n⟩` on `ℂ^(ℤ⁴)`. -/
noncomputable def chargeNumberOp (i : SpinBranch) : Module.End ℂ ChargeSpace :=
  Finsupp.lsum ℂ (fun n => LinearMap.toSpanSingleton ℂ ChargeSpace ((n i : ℂ) • chargeKet n))

lemma fourKleinOp_ket (i : SpinBranch) (n : SpinBranch → ℤ) :
    fourKleinOp i (chargeKet n) =
      (precedingParitySign i n : ℂ) • chargeKet (n - chargeBasisVec i) := by
  simp only [fourKleinOp, Module.End.mul_apply, chargeTranslationOp, precedingParityOp, chargeKet,
    Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, one_smul]
  congr 1
  rw [precedingParitySign_eq_epsZ4, precedingParitySign_eq_epsZ4, epsZ4_sub_right, epsZ4_basis_self,
    mul_one]

lemma fourKleinOp_eq_cocycleShift (i : SpinBranch) :
    fourKleinOp i = cocycleShift (chargeBasisVec i) := by
  apply Finsupp.lhom_ext'
  intro n
  apply LinearMap.ext_ring
  change fourKleinOp i (chargeKet n) = cocycleShift (chargeBasisVec i) (chargeKet n)
  rw [fourKleinOp_ket, cocycleShift_ket, precedingParitySign_eq_epsZ4]

lemma fourKleinAdj_ket (i : SpinBranch) (n : SpinBranch → ℤ) :
    fourKleinAdj i (chargeKet n) =
      (precedingParitySign i n : ℂ) • chargeKet (n + chargeBasisVec i) := by
  rw [fourKleinAdj, cocycleShift_ket, epsZ4_neg_left, ← precedingParitySign_eq_epsZ4, sub_neg_eq_add]

lemma fourKleinAdj_is_adjoint (i : SpinBranch) (u v : ChargeSpace) :
    chargeInner u (fourKleinOp i v) = chargeInner (fourKleinAdj i u) v := by
  induction u using Finsupp.induction_linear with
  | zero =>
    simp [chargeInner, map_zero]
  | add u₁ u₂ h₁ h₂ =>
    simp only [chargeInner, map_add] at h₁ h₂ ⊢
    rw [Finsupp.sum_add_index' (by intro n; simp) (by intro n c₁ c₂; simp [star_add, add_mul]),
      Finsupp.sum_add_index' (by intro n; simp) (by intro n c₁ c₂; simp [star_add, add_mul]),
      h₁, h₂]
  | single m a =>
    induction v using Finsupp.induction_linear with
    | zero =>
      simp [chargeInner, map_zero]
    | add v₁ v₂ h₁ h₂ =>
      simp only [chargeInner, map_add, Finsupp.add_apply, mul_add] at h₁ h₂ ⊢
      rw [Finsupp.sum_add, Finsupp.sum_add, h₁, h₂]
    | single n b =>
      have hF : fourKleinOp i (Finsupp.single n b) =
          (b * (precedingParitySign i n : ℂ)) • chargeKet (n - chargeBasisVec i) := by
        have h1 : Finsupp.single n b = b • chargeKet n := by
          simp [chargeKet, Finsupp.smul_single]
        rw [h1, map_smul, fourKleinOp_ket, smul_smul]
      have hA : fourKleinAdj i (Finsupp.single m a) =
          (a * (precedingParitySign i m : ℂ)) • chargeKet (m + chargeBasisVec i) := by
        have h1 : Finsupp.single m a = a • chargeKet m := by
          simp [chargeKet, Finsupp.smul_single]
        rw [h1, map_smul, fourKleinAdj_ket, smul_smul]
      rw [hF, hA]
      unfold chargeInner
      rw [Finsupp.sum_single_index (by simp)]
      have hAsingle :
          (a * (precedingParitySign i m : ℂ)) • chargeKet (m + chargeBasisVec i) =
            Finsupp.single (m + chargeBasisVec i) (a * (precedingParitySign i m : ℂ)) := by
        simp [chargeKet, Finsupp.smul_single]
      rw [hAsingle, Finsupp.sum_single_index (by simp)]
      simp only [chargeKet, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases hmn : m + chargeBasisVec i = n
      · subst hmn
        have hsub : m + chargeBasisVec i - chargeBasisVec i = m := by ext ν; simp
        have hsign : precedingParitySign i (m + chargeBasisVec i) = precedingParitySign i m := by
          rw [precedingParitySign_eq_epsZ4, precedingParitySign_eq_epsZ4, epsZ4_add_right,
            epsZ4_basis_self, mul_one]
        simp only [hsub, ↓reduceIte, mul_one, hsign, star_mul, star_intCast]
        ring
      · have hne : n - chargeBasisVec i ≠ m := by
          intro heq
          apply hmn
          rw [← heq]
          ext ν; simp
        simp [Ne.symm hmn, hne]

/-- Unitarity `F_i† F_i = I` on `ℂ^(ℤ⁴)`. -/
theorem fourKleinOp_unitary_left (i : SpinBranch) :
    fourKleinAdj i * fourKleinOp i = 1 := by
  rw [fourKleinAdj, fourKleinOp_eq_cocycleShift, cocycleShift_mul, neg_add_cancel, cocycleShift_zero,
    epsZ4_neg_left, epsZ4_basis_self]
  simp

/-- Unitarity `F_i F_i† = I` on `ℂ^(ℤ⁴)`. -/
theorem fourKleinOp_unitary_right (i : SpinBranch) :
    fourKleinOp i * fourKleinAdj i = 1 := by
  rw [fourKleinAdj, fourKleinOp_eq_cocycleShift, cocycleShift_mul, add_neg_cancel, cocycleShift_zero,
    epsZ4_neg_right, epsZ4_basis_self]
  simp

/-- Proposition `prop:ch21-klein-anticommute` (1): `F_i F_j = -F_j F_i` (`{F_i, F_j} = 0`) for `i ≠ j`. -/
theorem fourKleinOp_anticommute (i j : SpinBranch) (hne : i ≠ j) :
    fourKleinOp i * fourKleinOp j = -(fourKleinOp j * fourKleinOp i) := by
  rw [fourKleinOp_eq_cocycleShift, fourKleinOp_eq_cocycleShift, cocycleShift_mul, cocycleShift_mul,
    add_comm (chargeBasisVec j), epsZ4_basis_anticommute i j hne, Int.cast_neg]
  apply LinearMap.ext; intro v; simp [neg_smul]

theorem fourKleinOp_anticommutator_zero (i j : SpinBranch) (hne : i ≠ j) :
    fourKleinOp i * fourKleinOp j + fourKleinOp j * fourKleinOp i = 0 := by
  rw [fourKleinOp_anticommute i j hne]
  abel

/-- Proposition `prop:ch21-klein-anticommute` (2): `F_i F_j† = -F_j† F_i` (`{F_i, F_j†} = 0`) for `i ≠ j`. -/
theorem fourKleinOp_adj_anticommute (i j : SpinBranch) (hne : i ≠ j) :
    fourKleinOp i * fourKleinAdj j = -(fourKleinAdj j * fourKleinOp i) := by
  rw [fourKleinOp_eq_cocycleShift, fourKleinAdj, cocycleShift_mul, cocycleShift_mul,
    add_comm (-chargeBasisVec j), epsZ4_neg_right, epsZ4_neg_left, epsZ4_basis_anticommute i j hne,
    Int.cast_neg]
  apply LinearMap.ext; intro v; simp [neg_smul]

theorem fourKleinOp_adj_anticommutator_zero (i j : SpinBranch) (hne : i ≠ j) :
    fourKleinOp i * fourKleinAdj j + fourKleinAdj j * fourKleinOp i = 0 := by
  rw [fourKleinOp_adj_anticommute i j hne]
  abel

/-- Proposition `prop:ch21-klein-anticommute` (3): `[N_i, F_j] = -δ_{ij} F_j`. -/
theorem fourKleinOp_number_commutator (i j : SpinBranch) :
    A02.commutator (chargeNumberOp i) (fourKleinOp j) =
      -(if i = j then (1 : ℂ) else 0) • fourKleinOp j := by
  apply Finsupp.lhom_ext'
  intro n
  apply LinearMap.ext_ring
  change chargeNumberOp i (fourKleinOp j (chargeKet n)) -
      fourKleinOp j (chargeNumberOp i (chargeKet n)) =
    (-(if i = j then (1 : ℂ) else 0)) • fourKleinOp j (chargeKet n)
  have hnum (m : SpinBranch → ℤ) :
      chargeNumberOp i (chargeKet m) = (m i : ℂ) • chargeKet m := by
    simp [chargeNumberOp, chargeKet]
  rw [fourKleinOp_ket, hnum, map_smul, map_smul, hnum, fourKleinOp_ket, smul_smul, smul_smul,
    smul_smul]
  rw [← sub_smul]
  congr 1
  simp only [Pi.sub_apply, chargeBasisVec]
  by_cases hij : i = j
  · simp [hij]; ring
  · simp [hij]; ring

/-! ### 1.2 Finite `ℤ₂⁴` Clifford/Majorana Klein Operators (`K_i² = I`, `K_i K_j = -K_j K_i`) -/

/-- Finite 16-dimensional parity charge space `(Fin 4 → Bool) → ℂ` (`ℂ^(ℤ₂⁴)`). -/
abbrev ParityChargeSpace := (SpinBranch → Bool) → ℂ

/-- Preceding-bit parity sign `∏_{j < i} (-1)^{b_j} ∈ {±1}` on `ℤ₂⁴`. -/
def parityBitSign (i : SpinBranch) (b : SpinBranch → Bool) : ℂ :=
  (intParitySign (∑ j ∈ Finset.univ.filter (· < i), if b j then (1 : ℤ) else 0) : ℂ)

/-- Flip species bit `i` in `b : Fin 4 → Bool`. -/
def flipBit (i : SpinBranch) (b : SpinBranch → Bool) : SpinBranch → Bool :=
  Function.update b i (!(b i))

lemma flipBit_involutive (i : SpinBranch) (b : SpinBranch → Bool) :
    flipBit i (flipBit i b) = b := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [flipBit]
  · simp [flipBit, hk]

lemma flipBit_comm (i j : SpinBranch) (hne : i ≠ j) (b : SpinBranch → Bool) :
    flipBit i (flipBit j b) = flipBit j (flipBit i b) := by
  funext k
  by_cases hki : k = i
  · subst hki; simp [flipBit, hne]
  · by_cases hkj : k = j
    · subst hkj; simp [flipBit, hne.symm]
    · simp [flipBit, hki, hkj]

lemma parityBitSign_flipBit (i j : SpinBranch) (b : SpinBranch → Bool) :
    parityBitSign i (flipBit j b) = if j < i then -parityBitSign i b else parityBitSign i b := by
  unfold parityBitSign
  by_cases hlt : j < i
  · simp only [hlt, ↓reduceIte]
    have hmem : j ∈ Finset.univ.filter (· < i) := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hlt⟩
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
    have hrest :
        (∑ x ∈ (Finset.univ.filter (· < i)).erase j, if flipBit j b x then (1 : ℤ) else 0) =
          ∑ x ∈ (Finset.univ.filter (· < i)).erase j, if b x then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hne : x ≠ j := (Finset.mem_erase.mp hx).1
      simp [flipBit, hne]
    rw [hrest, intParitySign_add, intParitySign_add]
    have hflip : intParitySign (if flipBit j b j then (1 : ℤ) else 0) =
        -intParitySign (if b j then (1 : ℤ) else 0) := by
      simp only [flipBit, Function.update_self]
      cases b j <;> simp [intParitySign]
    rw [hflip]
    push_cast
    ring
  · simp only [hlt, ↓reduceIte]
    congr 2
    apply Finset.sum_congr rfl
    intro x hx
    have hxi : x < i := (Finset.mem_filter.mp hx).2
    have hne : x ≠ j := fun he => hlt (he ▸ hxi)
    simp [flipBit, hne]

/-- Hermitian involution four-species Klein operator `K_i` on `ℂ^(ℤ₂⁴)`:
`(K_i f)(b) = P_{<i}(b) f(flip_i b)`. -/
noncomputable def fourKleinMod2Op (i : SpinBranch) : Module.End ℂ ParityChargeSpace where
  toFun f b := parityBitSign i b * f (flipBit i b)
  map_add' f g := by funext b; simp [mul_add]
  map_smul' c f := by funext b; simp; ring

/-- Involution `K_i² = I` on `ℂ^(ℤ₂⁴)`. -/
theorem fourKleinMod2Op_sq (i : SpinBranch) :
    fourKleinMod2Op i * fourKleinMod2Op i = 1 := by
  apply LinearMap.ext
  intro f
  funext b
  simp only [Module.End.mul_apply, Module.End.one_apply, fourKleinMod2Op, LinearMap.coe_mk,
    AddHom.coe_mk, parityBitSign_flipBit, lt_irrefl, ↓reduceIte, flipBit_involutive]
  rw [← mul_assoc]
  unfold parityBitSign
  rw [← Int.cast_mul, intParitySign_sq]
  simp

/-- Mutual anticommutation `K_i K_j = -K_j K_i` for `i ≠ j` on `ℂ^(ℤ₂⁴)`. -/
theorem fourKleinMod2Op_anticommute (i j : SpinBranch) (hne : i ≠ j) :
    fourKleinMod2Op i * fourKleinMod2Op j = -(fourKleinMod2Op j * fourKleinMod2Op i) := by
  apply LinearMap.ext
  intro f
  funext b
  simp only [Module.End.mul_apply, LinearMap.neg_apply, Pi.neg_apply, fourKleinMod2Op,
    LinearMap.coe_mk, AddHom.coe_mk, parityBitSign_flipBit]
  rw [flipBit_comm j i hne.symm b]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hnot : ¬ j < i := not_lt_of_gt hlt
    simp only [hlt, hnot, ↓reduceIte]
    ring
  · have hnot : ¬ i < j := not_lt_of_gt hgt
    simp only [hgt, hnot, ↓reduceIte]
    ring

/-- Parity quotient `π : ℤ⁴ → ℤ₂⁴` reducing each species charge modulo 2. -/
def chargeMod2 (n : SpinBranch → ℤ) : SpinBranch → Bool :=
  fun ν => decide (n ν % 2 ≠ 0)

/-- Linear parity quotient `ℂ^(ℤ⁴) →ₗ[ℂ] ℂ^(ℤ₂⁴)` mapping `|n⟩ ↦ δ_{n mod 2}`. -/
noncomputable def chargeParityQuotient : ChargeSpace →ₗ[ℂ] ParityChargeSpace :=
  Finsupp.lsum ℂ (fun n => LinearMap.toSpanSingleton ℂ ParityChargeSpace
    (fun b => if b = chargeMod2 n then 1 else 0))

/-- Intertwining `π ∘ F_i = K_i ∘ π` connecting unitary `ℤ⁴` Klein factors with `ℤ₂⁴` involutions. -/
theorem chargeParityQuotient_intertwines (i : SpinBranch) :
    chargeParityQuotient ∘ₗ fourKleinOp i = fourKleinMod2Op i ∘ₗ chargeParityQuotient := by
  apply Finsupp.lhom_ext'
  intro n
  apply LinearMap.ext_ring
  funext b
  change chargeParityQuotient (fourKleinOp i (chargeKet n)) b =
    fourKleinMod2Op i (chargeParityQuotient (chargeKet n)) b
  rw [fourKleinOp_ket, map_smul]
  simp only [chargeParityQuotient, chargeKet, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    one_smul, Pi.smul_apply, smul_eq_mul, fourKleinMod2Op, LinearMap.coe_mk, AddHom.coe_mk]
  have hmod_sub : chargeMod2 (n - chargeBasisVec i) = flipBit i (chargeMod2 n) := by
    funext ν
    by_cases hν : ν = i
    · subst hν
      simp only [chargeMod2, Pi.sub_apply, chargeBasisVec, ↓reduceIte, flipBit,
        Function.update_self]
      have h2 := Int.emod_two_eq_zero_or_one (n ν)
      rcases h2 with h0 | h1
      · have hsub : (n ν - 1) % 2 = 1 := by omega
        simp [h0, hsub]
      · have hsub : (n ν - 1) % 2 = 0 := by omega
        simp [h1, hsub]
    · simp [chargeMod2, Pi.sub_apply, chargeBasisVec, hν, flipBit]
  have hflip_eq : (b = flipBit i (chargeMod2 n)) ↔ (flipBit i b = chargeMod2 n) := by
    constructor
    · intro h; rw [h, flipBit_involutive]
    · intro h; rw [← h, flipBit_involutive]
  rw [hmod_sub]
  by_cases hb : b = flipBit i (chargeMod2 n)
  · simp only [hb, flipBit_involutive, ↓reduceIte, mul_one]
    have hsign_eq : (precedingParitySign i n : ℂ) = parityBitSign i (chargeMod2 n) := by
      unfold precedingParitySign parityBitSign
      congr 1
      have hmod : (∑ j ∈ Finset.univ.filter (· < i), n j) % 2 =
          (∑ j ∈ Finset.univ.filter (· < i), if chargeMod2 n j then (1 : ℤ) else 0) % 2 := by
        have hstep : ∀ (s : Finset SpinBranch),
            (∑ j ∈ s, n j) % 2 =
              (∑ j ∈ s, if chargeMod2 n j then (1 : ℤ) else 0) % 2 := by
          intro s
          induction s using Finset.induction with
          | empty => simp
          | insert a s ha ih =>
            rw [Finset.sum_insert ha, Finset.sum_insert ha, Int.add_emod,
              Int.add_emod (if chargeMod2 n a then (1 : ℤ) else 0), ih]
            have ha2 := Int.emod_two_eq_zero_or_one (n a)
            rcases ha2 with h0 | h1
            · simp [chargeMod2, h0]
            · simp [chargeMod2, h1]
        exact hstep (Finset.univ.filter (· < i))
      unfold intParitySign
      rw [hmod]
    rw [hsign_eq, parityBitSign_flipBit]
    simp
  · have hb' : flipBit i b ≠ chargeMod2 n := fun h => hb (hflip_eq.mpr h)
    simp [hb, hb']

/-! ## 2. First-Mode Oscillator & Off-Margin Commutator Counterexample (`ex:ch21-first-mode`, `eq:ch21-off-margin-example`, `eq:ch21-compression-residual`) -/

/-- `ex:ch21-first-mode` (`eq:ch21-example-two`): on the zero-charge sea `Ω₀` for any `h ≥ 2`,
`[R^c_{L,-1}, R^c_{L,1}] Ω₀ = 2 Ω₀`, `[R^s_{L,-1}, R^s_{L,1}] Ω₀ = 2 Ω₀`, and
`[R^c_{L,-1}, R^s_{L,1}] Ω₀ = 0`. -/
theorem first_mode_charge_spin_commutators (h : ℕ) (hh : 2 ≤ h) :
    A02.commutator (rhoChargeL h (-1)) (rhoChargeL h 1) (A05.groundKet h (fun _ => 0)) =
      (2 : ℂ) • A05.groundKet h (fun _ => 0) ∧
    A02.commutator (rhoSpinL h (-1)) (rhoSpinL h 1) (A05.groundKet h (fun _ => 0)) =
      (2 : ℂ) • A05.groundKet h (fun _ => 0) ∧
    A02.commutator (rhoChargeL h (-1)) (rhoSpinL h 1) (A05.groundKet h (fun _ => 0)) = 0 := by
  have hpos : 0 < h := by omega
  have hmem : A05.groundKet h (fun _ => 0) ∈ A05.jointBudget h (fun _ => 0) 0 :=
    A05.ground_mem_budget h hpos (fun _ => 0) (zeroCharge_admissible h) 0
  have hmargin : |(-1 : ℤ)| + |(1 : ℤ)| + ((0 : ℕ) : ℤ) + |(0 : ℤ)| ≤ (h : ℤ) := by norm_num; omega
  have hschw : (2 : ℂ) * Ch10.schwingerCoefficient (-1) 1 = (2 : ℂ) := by
    simp [Ch10.schwingerCoefficient]
  refine ⟨?_, ?_, ?_⟩
  · rw [rhoChargeL_commutator h 0 hpos (fun _ => 0) (-1) 1 hmargin hmargin _ hmem, hschw]
  · rw [rhoSpinL_commutator h 0 hpos (fun _ => 0) (-1) 1 hmargin hmargin _ hmem, hschw]
  · exact rhoChargeL_rhoSpinL_commutator h 0 hpos (fun _ => 0) (-1) 1 hmargin hmargin _ hmem

theorem first_mode_charge_spin_commutators_h2 :
    A02.commutator (rhoChargeL 2 (-1)) (rhoChargeL 2 1) (A05.groundKet 2 (fun _ => 0)) =
      (2 : ℂ) • A05.groundKet 2 (fun _ => 0) ∧
    A02.commutator (rhoSpinL 2 (-1)) (rhoSpinL 2 1) (A05.groundKet 2 (fun _ => 0)) =
      (2 : ℂ) • A05.groundKet 2 (fun _ => 0) ∧
    A02.commutator (rhoChargeL 2 (-1)) (rhoSpinL 2 1) (A05.groundKet 2 (fun _ => 0)) = 0 :=
  first_mode_charge_spin_commutators 2 (le_refl 2)

/-- Off-margin charge vector `(h, 0, 0, 0)`: `L↑` completely filled, `L↓, R↑, R↓` in the sea ground. -/
def offMarginChargeL (h : ℕ) (ν : SpinBranch) : ℤ :=
  if ν = brLUp then (h : ℤ) else 0

lemma offMarginChargeL_admissible (h : ℕ) : A05.admissible h (offMarginChargeL h) := by
  intro ν
  fin_cases ν <;> simp [Ch07.admissible, offMarginChargeL, brLUp]

/-- Explicit off-margin counterexample ket `v = |full_{L↑}, sea_{L↓}, sea_{R↑}, sea_{R↓}⟩`
(`eq:ch21-off-margin-example`). -/
noncomputable def offMarginKetL (h : ℕ) : A05.FockSpace SpinBranch h :=
  A05.groundKet h (offMarginChargeL h)

lemma offMarginKetL_ne_zero (h : ℕ) : offMarginKetL h ≠ 0 := by
  unfold offMarginKetL A05.groundKet
  exact A02.ket_ne_zero _

/-- Every nonzero-momentum density operator `ρ_{L↑, m}` (`m ≠ 0`) annihilates the full `L↑` band. -/
lemma rho_full_band_annihilates (h : ℕ) (m : ℤ) (hm : m ≠ 0) :
    A05.rho h brLUp m (offMarginKetL h) = 0 := by
  unfold offMarginKetL A05.groundKet A05.rho
  simp only [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro z hz
  have hz_eq : z.1.val = z.2.val + m := (Finset.mem_filter.mp hz).2
  have hne : (brLUp, z.1) ≠ (brLUp, z.2) := by
    intro heq
    have hval : z.1.val = z.2.val := congrArg (fun p : A05.Mode SpinBranch h => p.2.val) heq
    omega
  have hmem : (brLUp, z.1) ∈ A05.groundConfiguration h (offMarginChargeL h) := by
    simp only [A05.groundConfiguration, A05.jointConfiguration, Finset.mem_biUnion, Finset.mem_univ,
      true_and, Finset.mem_image]
    refine ⟨brLUp, z.1, ?_, rfl⟩
    simp only [Ch07.groundConfiguration, Finset.mem_filter, Finset.mem_univ, true_and]
    change z.1.val ≤ (h : ℤ)
    have hband := z.1.property
    simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hband
    omega
  exact Ch04.hopping_blocked (brLUp, z.1) (brLUp, z.2) _ (Or.inr ⟨hne, hmem⟩)

/-- Exact off-margin counterexample (`eq:ch21-off-margin-example`): for every `h ≥ 2`,
`[R^c_{L,-1}, R^s_{L,1}] v = -v` on the nonzero product ket `v = offMarginKetL h`. -/
theorem off_margin_commutator_counterexample (h : ℕ) (hh : 2 ≤ h) :
    A02.commutator (rhoChargeL h (-1)) (rhoSpinL h 1) (offMarginKetL h) = -(offMarginKetL h) := by
  have hpos : 0 < h := by omega
  rw [rhoChargeL_rhoSpinL_global_edge h (-1) 1, LinearMap.sub_apply]
  have hUp : edgeOp h brLUp (-1) 1 (offMarginKetL h) = 0 := by
    simp only [edgeOp, A02.commutator, LinearMap.sub_apply, Module.End.mul_apply,
      rho_full_band_annihilates h 1 (by norm_num),
      rho_full_band_annihilates h (-1) (by norm_num), map_zero, sub_self]
  have hDown : edgeOp h brLDown (-1) 1 (offMarginKetL h) = offMarginKetL h := by
    have hmem : offMarginKetL h ∈ A05.jointBudget h (offMarginChargeL h) 0 :=
      A05.ground_mem_budget h hpos (offMarginChargeL h) (offMarginChargeL_admissible h) 0
    have hmargin : |(-1 : ℤ)| + |(1 : ℤ)| + ((0 : ℕ) : ℤ) + |offMarginChargeL h brLDown| ≤ (h : ℤ) := by
      simp only [offMarginChargeL, brLDown, brLUp]
      norm_num
      omega
    have hccr := A06.joint_signed_current_commutator h 0 hpos (offMarginChargeL h) brLDown
      (-1) 1 hmargin (offMarginKetL h) hmem
    unfold edgeOp
    rw [hccr]
    simp [Ch10.schwingerCoefficient]
  rw [hUp, hDown, zero_sub]

/-- Concrete `h = 2` off-margin counterexample: `[R^c_{L,-1}, R^s_{L,1}] v = -v ≠ 0`. -/
theorem off_margin_commutator_counterexample_h2 :
    A02.commutator (rhoChargeL 2 (-1)) (rhoSpinL 2 1) (offMarginKetL 2) = -(offMarginKetL 2) ∧
    A02.commutator (rhoChargeL 2 (-1)) (rhoSpinL 2 1) (offMarginKetL 2) ≠ 0 := by
  have heq := off_margin_commutator_counterexample 2 (le_refl 2)
  exact ⟨heq, by rw [heq]; exact neg_ne_zero.mpr (offMarginKetL_ne_zero 2)⟩

/-- Unrestricted global spin-charge commutation fails on the finite CAR carrier for every `h ≥ 2`. -/
theorem rhoChargeL_rhoSpinL_global_ne_zero (h : ℕ) (hh : 2 ≤ h) :
    A02.commutator (rhoChargeL h (-1)) (rhoSpinL h 1) ≠ 0 := by
  intro hzero
  have hv := off_margin_commutator_counterexample h hh
  rw [hzero, LinearMap.zero_apply] at hv
  exact offMarginKetL_ne_zero h (neg_eq_zero.mp hv.symm)

/-- Exact compressed-commutator residual identity (`eq:ch21-compression-residual`):
for any idempotent projector `P² = P` with complement `Q = 1 - P` and arbitrary operators `A, B`,
`[P A P, P B P] = P [A, B] P - P A Q B P + P B Q A P`. -/
theorem compressed_commutator_residual {V : Type*} [AddCommGroup V] [Module ℂ V]
    (P A B : Module.End ℂ V) (hP : P * P = P) :
    A02.commutator (P * A * P) (P * B * P) =
      P * A02.commutator A B * P - P * A * (1 - P) * B * P + P * B * (1 - P) * A * P := by
  simp only [A02.commutator, mul_sub, sub_mul, mul_one, mul_assoc]
  have h1 : P * (A * (P * (P * (B * P)))) = P * (A * (P * (B * P))) := by
    rw [← mul_assoc P P, hP]
  have h2 : P * (B * (P * (P * (A * P)))) = P * (B * (P * (A * P))) := by
    rw [← mul_assoc P P, hP]
  rw [h1, h2]
  abel

/-! ## 3. Spinful Charge/Spin Hyperbolic Quadratic Block Diagonalization (`prop:ch21-quadratic-block`, `eq:ch21-hyperbolic-parameters`, `ex:ch21-equal-speeds`) -/

/-- Proposition `prop:ch21-quadratic-block` (`eq:ch21-quadratic-block`):
ordered noncommutative quadratic block diagonalization for exchange-symmetric couplings. -/
theorem ordered_quadratic_block_diagonalization {R : Type*} [Ring R] [Algebra ℂ R]
    (a b : ℂ) (XUp XDown YUp YDown : R) :
    let Xc := XUp + XDown
    let Xs := XUp - XDown
    let Yc := YUp + YDown
    let Ys := YUp - YDown
    a • (XUp * YUp + XDown * YDown) + b • (XUp * YDown + XDown * YUp) =
      ((a + b) / 2) • (Xc * Yc) + ((a - b) / 2) • (Xs * Ys) := by
  dsimp only
  have hXc : (XUp + XDown) * (YUp + YDown) =
      XUp * YUp + XUp * YDown + XDown * YUp + XDown * YDown := by noncomm_ring
  have hXs : (XUp - XDown) * (YUp - YDown) =
      XUp * YUp - XUp * YDown - XDown * YUp + XDown * YDown := by noncomm_ring
  rw [hXc, hXs]
  have hsum : (a + b) / 2 + (a - b) / 2 = a := by ring
  have hdiff : (a + b) / 2 - (a - b) / 2 = b := by ring
  simp only [smul_add, smul_sub]
  calc
    a • (XUp * YUp) + a • (XDown * YDown) + (b • (XUp * YDown) + b • (XDown * YUp))
        = ((a + b) / 2 + (a - b) / 2) • (XUp * YUp) +
          ((a + b) / 2 + (a - b) / 2) • (XDown * YDown) +
          (((a + b) / 2 - (a - b) / 2) • (XUp * YDown) +
           ((a + b) / 2 - (a - b) / 2) • (XDown * YUp)) := by rw [hsum, hdiff]
    _ = ((a + b) / 2) • (XUp * YUp) + ((a + b) / 2) • (XUp * YDown) +
          ((a + b) / 2) • (XDown * YUp) + ((a + b) / 2) • (XDown * YDown) +
          (((a - b) / 2) • (XUp * YUp) - ((a - b) / 2) • (XUp * YDown) -
            ((a - b) / 2) • (XDown * YUp) + ((a - b) / 2) • (XDown * YDown)) := by
          simp only [add_smul, sub_smul]
          abel

/-- Spin-dependent diagonal coupling mixing identity (`eq:ch21-asymmetry-mixes`). -/
theorem asymmetric_quadratic_mixes_charge_spin {R : Type*} [Ring R] [Algebra ℂ R]
    (aUp aDown : ℂ) (XUp XDown YUp YDown : R) :
    let Xc := XUp + XDown
    let Xs := XUp - XDown
    let Yc := YUp + YDown
    let Ys := YUp - YDown
    aUp • (XUp * YUp) + aDown • (XDown * YDown) =
      ((aUp + aDown) / 4) • (Xc * Yc + Xs * Ys) +
      ((aUp - aDown) / 4) • (Xc * Ys + Xs * Yc) := by
  dsimp only
  have h1 : (XUp + XDown) * (YUp + YDown) + (XUp - XDown) * (YUp - YDown) =
      (2 : ℂ) • (XUp * YUp + XDown * YDown) := by
    rw [two_smul]
    noncomm_ring
  have h2 : (XUp + XDown) * (YUp - YDown) + (XUp - XDown) * (YUp + YDown) =
      (2 : ℂ) • (XUp * YUp - XDown * YDown) := by
    rw [two_smul]
    noncomm_ring
  rw [h1, h2, smul_smul, smul_smul, smul_add, smul_sub]
  have hp : (aUp + aDown) / 4 * 2 + (aUp - aDown) / 4 * 2 = aUp := by ring
  have hm : (aUp + aDown) / 4 * 2 - (aUp - aDown) / 4 * 2 = aDown := by ring
  calc
    aUp • (XUp * YUp) + aDown • (XDown * YDown)
        = ((aUp + aDown) / 4 * 2 + (aUp - aDown) / 4 * 2) • (XUp * YUp) +
          ((aUp + aDown) / 4 * 2 - (aUp - aDown) / 4 * 2) • (XDown * YDown) := by rw [hp, hm]
    _ = ((aUp + aDown) / 4 * 2) • (XUp * YUp) + ((aUp + aDown) / 4 * 2) • (XDown * YDown) +
        (((aUp - aDown) / 4 * 2) • (XUp * YUp) - ((aUp - aDown) / 4 * 2) • (XDown * YDown)) := by
          simp only [add_smul, sub_smul]
          abel

/-- Stability equivalence `|g₂| < 2π v_F + g₄ ↔ |v₂| < v₁` for `Ch17.v1Velocity` / `Ch17.v2Velocity`. -/
lemma spinful_block_stability_iff (vF g4 g2 : ℝ) :
    |g2| < 2 * Real.pi * vF + g4 ↔ |Ch17.v2Velocity g2| < Ch17.v1Velocity vF g4 := by
  have h2pi : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  unfold Ch17.v1Velocity Ch17.v2Velocity
  rw [abs_div, abs_of_pos h2pi]
  constructor
  · intro h
    have hdiv : |g2| / (2 * Real.pi) < (2 * Real.pi * vF + g4) / (2 * Real.pi) :=
      div_lt_div_of_pos_right h h2pi
    have hsimp : (2 * Real.pi * vF + g4) / (2 * Real.pi) = vF + g4 / (2 * Real.pi) := by
      field_simp [h2pi.ne']
    linarith
  · intro h
    have hmul : (|g2| / (2 * Real.pi)) * (2 * Real.pi) < (vF + g4 / (2 * Real.pi)) * (2 * Real.pi) :=
      mul_lt_mul_of_pos_right h h2pi
    have hL : (|g2| / (2 * Real.pi)) * (2 * Real.pi) = |g2| := div_mul_cancel₀ _ h2pi.ne'
    have hR : (vF + g4 / (2 * Real.pi)) * (2 * Real.pi) = 2 * Real.pi * vF + g4 := by
      field_simp [h2pi.ne']
    linarith

/-- Independent charge and spin hyperbolic Bogoliubov parameters (`eq:ch21-hyperbolic-parameters`). -/
structure SpinfulHyperbolicBlocks (vF g4c g2c g4s g2s : ℝ) where
  charge : A07Interactions.HyperbolicParams (Ch17.v1Velocity vF g4c) (Ch17.v2Velocity g2c)
  spin : A07Interactions.HyperbolicParams (Ch17.v1Velocity vF g4s) (Ch17.v2Velocity g2s)

/-- Charge-sector Luttinger parameter `K_c = (c_c - s_c)²`. -/
noncomputable def SpinfulHyperbolicBlocks.Kc {vF g4c g2c g4s g2s : ℝ}
    (B : SpinfulHyperbolicBlocks vF g4c g2c g4s g2s) : ℝ :=
  Ch18.luttingerG (Ch18.HyperbolicPair.ofParams B.charge)

/-- Spin-sector Luttinger parameter `K_s = (c_s - s_s)²`. -/
noncomputable def SpinfulHyperbolicBlocks.Ks {vF g4c g2c g4s g2s : ℝ}
    (B : SpinfulHyperbolicBlocks vF g4c g2c g4s g2s) : ℝ :=
  Ch18.luttingerG (Ch18.HyperbolicPair.ofParams B.spin)

/-- Independent existence of charge `(u_c, K_c)` and spin `(u_s, K_s)` hyperbolic parameters
whenever `|g_{2,c}| < 2π v_F + g_{4,c}` and `|g_{2,s}| < 2π v_F + g_{4,s}`. -/
theorem spinful_hyperbolic_blocks_nonempty (vF g4c g2c g4s g2s : ℝ)
    (hc : |g2c| < 2 * Real.pi * vF + g4c)
    (hs : |g2s| < 2 * Real.pi * vF + g4s) :
    Nonempty (SpinfulHyperbolicBlocks vF g4c g2c g4s g2s) := by
  have h1 := Ch18.hyperbolic_params_nonempty (Ch17.v1Velocity vF g4c) (Ch17.v2Velocity g2c)
    ((spinful_block_stability_iff vF g4c g2c).mp hc)
  have h2 := Ch18.hyperbolic_params_nonempty (Ch17.v1Velocity vF g4s) (Ch17.v2Velocity g2s)
    ((spinful_block_stability_iff vF g4s g2s).mp hs)
  exact ⟨⟨Classical.choice h1, Classical.choice h2⟩⟩

/-- `2×2` Bogoliubov dynamical matrix `M(v₁, v₂) = [[v₁, v₂], [-v₂, -v₁]]` (`eq:ch21-bogoliubov-dynamic`). -/
def bogoliubovDynMatrix (v1 v2 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![v1, v2; -v2, -v1]

/-- Hyperbolic squeezing matrix `B(c, s) = [[c, s], [s, c]]` and its inverse `[[c, -s], [-s, c]]`. -/
def bogoliubovTransformMatrix (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c, s; s, c]

def bogoliubovTransformInvMatrix (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c, -s; -s, c]

/-- Exact `2×2` hyperbolic diagonalization `B M B⁻¹ = diag(u, -u)` for any `HyperbolicParams v1 v2`. -/
theorem bogoliubov_block_diagonalizes {v1 v2 : ℝ}
    (hp : A07Interactions.HyperbolicParams v1 v2) :
    bogoliubovTransformMatrix hp.c hp.s * bogoliubovTransformInvMatrix hp.c hp.s = 1 ∧
    bogoliubovTransformInvMatrix hp.c hp.s * bogoliubovTransformMatrix hp.c hp.s = 1 ∧
    bogoliubovTransformMatrix hp.c hp.s * bogoliubovDynMatrix v1 v2 *
        bogoliubovTransformInvMatrix hp.c hp.s = !![hp.u, 0; 0, -hp.u] := by
  rcases hp with ⟨u, c, s, _, _, _, hid, hv1, hv2⟩
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [bogoliubovTransformMatrix, bogoliubovTransformInvMatrix, Matrix.mul_apply,
        Fin.sum_univ_two] <;> nlinarith
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [bogoliubovTransformMatrix, bogoliubovTransformInvMatrix, Matrix.mul_apply,
        Fin.sum_univ_two] <;> nlinarith
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [bogoliubovTransformMatrix, bogoliubovTransformInvMatrix, bogoliubovDynMatrix,
        Matrix.mul_apply, Fin.sum_univ_two]
    · rw [hv1, hv2]
      have hfac : (c * (u * (c ^ 2 + s ^ 2)) + -(s * (2 * u * c * s))) * c +
          -((c * (2 * u * c * s) + -(s * (u * (c ^ 2 + s ^ 2)))) * s) =
          u * (c ^ 2 - s ^ 2) ^ 2 := by ring
      rw [hfac, hid]; ring
    · rw [hv1, hv2]; ring
    · rw [hv1, hv2]; ring
    · rw [hv1, hv2]
      have hfac : -((s * (u * (c ^ 2 + s ^ 2)) + -(c * (2 * u * c * s))) * s) +
          (s * (2 * u * c * s) + -(c * (u * (c ^ 2 + s ^ 2)))) * c =
          -(u * (c ^ 2 - s ^ 2) ^ 2) := by ring
      rw [hfac, hid]; ring

/-- Independent Bogoliubov diagonalization of both charge `(u_c, K_c)` and spin `(u_s, K_s)` blocks
together with the hyperbolic parameter identities (`eq:ch21-hyperbolic-parameters`). -/
theorem spinful_charge_spin_diagonalization {vF g4c g2c g4s g2s : ℝ}
    (B : SpinfulHyperbolicBlocks vF g4c g2c g4s g2s) :
    (bogoliubovTransformMatrix B.charge.c B.charge.s *
        bogoliubovDynMatrix (Ch17.v1Velocity vF g4c) (Ch17.v2Velocity g2c) *
        bogoliubovTransformInvMatrix B.charge.c B.charge.s = !![B.charge.u, 0; 0, -B.charge.u]) ∧
    (bogoliubovTransformMatrix B.spin.c B.spin.s *
        bogoliubovDynMatrix (Ch17.v1Velocity vF g4s) (Ch17.v2Velocity g2s) *
        bogoliubovTransformInvMatrix B.spin.c B.spin.s = !![B.spin.u, 0; 0, -B.spin.u]) ∧
    B.charge.u = Real.sqrt (Ch17.v1Velocity vF g4c ^ 2 - Ch17.v2Velocity g2c ^ 2) ∧
    B.spin.u = Real.sqrt (Ch17.v1Velocity vF g4s ^ 2 - Ch17.v2Velocity g2s ^ 2) ∧
    B.Kc * B.charge.u = Ch17.v1Velocity vF g4c - Ch17.v2Velocity g2c ∧
    B.Ks * B.spin.u = Ch17.v1Velocity vF g4s - Ch17.v2Velocity g2s ∧
    B.Kc = Real.sqrt ((Ch17.v1Velocity vF g4c - Ch17.v2Velocity g2c) /
        (Ch17.v1Velocity vF g4c + Ch17.v2Velocity g2c)) ∧
    B.Ks = Real.sqrt ((Ch17.v1Velocity vF g4s - Ch17.v2Velocity g2s) /
        (Ch17.v1Velocity vF g4s + Ch17.v2Velocity g2s)) := by
  refine ⟨(bogoliubov_block_diagonalizes B.charge).2.2,
    (bogoliubov_block_diagonalizes B.spin).2.2, ?_, ?_,
    Ch18.luttingerG_mul_u_of_params B.charge,
    Ch18.luttingerG_mul_u_of_params B.spin,
    Ch18.luttingerG_eq_sqrt_of_params B.charge,
    Ch18.luttingerG_eq_sqrt_of_params B.spin⟩
  · rw [← B.charge.u_sq, Real.sqrt_sq B.charge.u_pos.le]
  · rw [← B.spin.u_sq, Real.sqrt_sq B.spin.u_pos.le]

/-- Speed non-degeneracy equivalence (`eq:ch21-speed-nondegeneracy`):
`u_c ≠ u_s ↔ v_{1,c}² - v_{2,c}² ≠ v_{1,s}² - v_{2,s}²`. -/
theorem spinful_speed_nondegeneracy_iff {v1c v2c v1s v2s : ℝ}
    (hc : A07Interactions.HyperbolicParams v1c v2c)
    (hs : A07Interactions.HyperbolicParams v1s v2s) :
    hc.u ≠ hs.u ↔ v1c ^ 2 - v2c ^ 2 ≠ v1s ^ 2 - v2s ^ 2 := by
  rw [← hc.u_sq, ← hs.u_sq]
  constructor
  · intro hne hsq
    apply hne
    have h0 : (hc.u - hs.u) * (hc.u + hs.u) = 0 := by nlinarith
    rcases mul_eq_zero.mp h0 with hsub | hadd
    · linarith
    · linarith [hc.u_pos, hs.u_pos]
  · intro hne heq
    exact hne (congrArg (· ^ 2) heq)

/-- Free hyperbolic parameters `HyperbolicParams v 0` with `(u, c, s) = (v, 1, 0)` for `v > 0`. -/
def freeHyperbolicParams (v : ℝ) (hv : 0 < v) : A07Interactions.HyperbolicParams v 0 where
  u := v
  c := 1
  s := 0
  u_pos := hv
  c_pos := one_pos
  u_sq := by ring
  hyperbolic_id := by norm_num
  match_v1 := by ring
  match_v2 := by ring

/-- Free-velocity hyperbolic parameters for `(Ch17.v1Velocity v 0, Ch17.v2Velocity 0)`. -/
noncomputable def freeBlockHyperbolicParams (v : ℝ) (hv : 0 < v) :
    A07Interactions.HyperbolicParams (Ch17.v1Velocity v 0) (Ch17.v2Velocity 0) where
  u := v
  c := 1
  s := 0
  u_pos := hv
  c_pos := one_pos
  u_sq := by simp [Ch17.v1Velocity, Ch17.v2Velocity]
  hyperbolic_id := by norm_num
  match_v1 := by simp [Ch17.v1Velocity]
  match_v2 := by simp [Ch17.v2Velocity]

/-- Explicit equal-speed degeneracy witness (`ex:ch21-equal-speeds`):
for any `v > 0` with `g_{4,c} = g_{2,c} = g_{4,s} = g_{2,s} = 0`, the charge and spin blocks
diagonalize cleanly yet satisfy `u_c = u_s = v` and `K_c = K_s = 1`. -/
noncomputable def equalSpeedWitness (v : ℝ) (hv : 0 < v) :
    SpinfulHyperbolicBlocks v 0 0 0 0 where
  charge := freeBlockHyperbolicParams v hv
  spin := freeBlockHyperbolicParams v hv

theorem equal_speed_witness_degenerate (v : ℝ) (hv : 0 < v) :
    (equalSpeedWitness v hv).charge.u = v ∧
    (equalSpeedWitness v hv).spin.u = v ∧
    (equalSpeedWitness v hv).charge.u = (equalSpeedWitness v hv).spin.u ∧
    (equalSpeedWitness v hv).Kc = 1 ∧
    (equalSpeedWitness v hv).Ks = 1 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · simp [SpinfulHyperbolicBlocks.Kc, Ch18.luttingerG, Ch18.HyperbolicPair.ofParams,
      equalSpeedWitness, freeBlockHyperbolicParams]
  · simp [SpinfulHyperbolicBlocks.Ks, Ch18.luttingerG, Ch18.HyperbolicPair.ofParams,
      equalSpeedWitness, freeBlockHyperbolicParams]

/-- Distinct-speed contrast witness from `ex:ch21-equal-speeds`:
`(v_{1,c}, v_{2,c}) = (17, 15)` gives `u_c = 8, K_c = 1/4` while `(v_{1,s}, v_{2,s}) = (5, 0)`
gives `u_s = 5, K_s = 1`, witnessing `u_c ≠ u_s`. -/
theorem distinct_speed_contrast_witness :
    let hc := Ch18.concreteParams
    let hs := freeHyperbolicParams 5 (by norm_num)
    hc.u = 8 ∧ hs.u = 5 ∧ hc.u ≠ hs.u ∧
    Ch18.luttingerG (Ch18.HyperbolicPair.ofParams hc) = 1 / 4 ∧
    Ch18.luttingerG (Ch18.HyperbolicPair.ofParams hs) = 1 := by
  dsimp [Ch18.concreteParams, freeHyperbolicParams, Ch18.luttingerG, Ch18.HyperbolicPair.ofParams]
  norm_num

/-! ## 4. General Per-Species Charge-Box Outward & Inward Leakage (`thm:ch21-u-leakage`) -/

/-- Summed forward (outward) Umklapp operator `∑_{x ∈ Λ_L} O_U(x)`. -/
noncomputable def umklappForwardSum (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) : A05.Operators SpinBranch h :=
  ∑ x : Fin (2 * h), umklappForwardSite h b (x.val : ℤ)

/-- Summed backward (inward) Umklapp operator `∑_{x ∈ Λ_L} O_U(x)†`. -/
noncomputable def umklappBackwardSum (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) : A05.Operators SpinBranch h :=
  ∑ x : Fin (2 * h), umklappBackwardSite h b (x.val : ℤ)

lemma umklappOp_eq_smul_add_sums (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (gU : ℝ) :
    umklappOp h b gU =
      ((gU : ℂ) / (2 * (h : ℂ))) • (umklappForwardSum h b + umklappBackwardSum h b) := by
  unfold umklappOp umklappForwardSum umklappBackwardSum
  rw [Finset.sum_add_distrib]

lemma umklappForwardSum_maps_sector (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h))
    (Ns : SpinBranch → ℤ) (ψ : A05.FockSpace SpinBranch h) (hψ : ψ ∈ chargeSector h Ns) :
    umklappForwardSum h b ψ ∈ chargeSector h (umklappForwardTarget Ns) := by
  unfold umklappForwardSum
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ (fun x _ => umklappForwardSite_maps_sector h b (x.val : ℤ) Ns ψ hψ)

lemma umklappBackwardSum_maps_sector (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h))
    (Ns : SpinBranch → ℤ) (ψ : A05.FockSpace SpinBranch h) (hψ : ψ ∈ chargeSector h Ns) :
    umklappBackwardSum h b ψ ∈ chargeSector h (umklappBackwardTarget Ns) := by
  unfold umklappBackwardSum
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ (fun x _ => umklappBackwardSite_maps_sector h b (x.val : ℤ) Ns ψ hψ)

/-- Any charge sector whose species charge `T_ν` exceeds `B_ν` is orthogonal to `ℬ_{K, B}`. -/
lemma chargeSector_orthogonal_speciesChargeBox (h K : ℕ) (B : SpinBranch → ℕ)
    (T : SpinBranch → ℤ) (hviol : ∃ ν, (B ν : ℤ) < |T ν|)
    (u : A05.FockSpace SpinBranch h) (hu : u ∈ chargeSector h T)
    (w : A05.FockSpace SpinBranch h) (hw : w ∈ speciesChargeBox h K B) :
    inner ℂ u w = 0 := by
  obtain ⟨ν, hν⟩ := hviol
  exact @A03.coordinate_space_disjoint (A05.Mode SpinBranch h) _ instDecidableEqProd _ _
    (by
      rw [Set.disjoint_left]
      intro S hST hSB
      have h1 : Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) = T ν := hST ν
      have h2 : |Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν)| ≤ (B ν : ℤ) := hSB.1 ν
      rw [h1] at h2
      omega)
    u hu w hw

/-- Theorem `thm:ch21-u-leakage` (outward branch): if `ψ ∈ ℬ_{K, B}` has definite charge `Ns`,
the outward Umklapp sum `∑_x O_U(x) ψ ≠ 0`, and some species exits the charge box bound
`|Ns ν + ΔN_ν| > B ν`, then for `h > 0` and `g_U ≠ 0`:
1. `H_U ψ ∉ ℬ_{K, B}`,
2. `[P_{K, B}, H_U] ψ ≠ 0`, and
3. `[P_{K, B}, H_U] ≠ 0`. -/
theorem umklapp_charge_box_outward_leakage (h K : ℕ) (hh : 0 < h)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (gU : ℝ) (hg : gU ≠ 0)
    (B : SpinBranch → ℕ) (Ns : SpinBranch → ℤ)
    (ψ : A05.FockSpace SpinBranch h)
    (hBox : ψ ∈ speciesChargeBox h K B)
    (hSec : ψ ∈ chargeSector h Ns)
    (hOut : umklappForwardSum h b ψ ≠ 0)
    (hExit : ∃ ν, (B ν : ℤ) < |umklappForwardTarget Ns ν|) :
    umklappOp h b gU ψ ∉ speciesChargeBox h K B ∧
    A02.commutator (speciesChargeBoxProjection h K B) (umklappOp h b gU) ψ ≠ 0 ∧
    A02.commutator (speciesChargeBoxProjection h K B) (umklappOp h b gU) ≠ 0 := by
  have hFsec : umklappForwardSum h b ψ ∈ chargeSector h (umklappForwardTarget Ns) :=
    umklappForwardSum_maps_sector h b Ns ψ hSec
  have hBsec : umklappBackwardSum h b ψ ∈ chargeSector h (umklappBackwardTarget Ns) :=
    umklappBackwardSum_maps_sector h b Ns ψ hSec
  have hFB0 : inner ℂ (umklappForwardSum h b ψ) (umklappBackwardSum h b ψ) = 0 :=
    distinct_charge_sectors_orthogonal h (umklappForwardTarget Ns) (umklappBackwardTarget Ns)
      (umklapp_targets_distinct Ns).2.2 _ hFsec _ hBsec
  have hcne : (gU : ℂ) / (2 * (h : ℂ)) ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr hg)
      (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hh)))
  have hinner_ne : inner ℂ (umklappForwardSum h b ψ) (umklappOp h b gU ψ) ≠ 0 := by
    rw [umklappOp_eq_smul_add_sums, LinearMap.smul_apply, LinearMap.add_apply, inner_smul_right,
      inner_add_right, hFB0, add_zero]
    exact mul_ne_zero hcne (fun h0 => hOut (inner_self_eq_zero.mp h0))
  have hnotmem : umklappOp h b gU ψ ∉ speciesChargeBox h K B := by
    intro hmem
    exact hinner_ne (chargeSector_orthogonal_speciesChargeBox h K B _ hExit _ hFsec _ hmem)
  have hPψ : speciesChargeBoxProjection h K B ψ = ψ :=
    (@A03.projection_fixed_iff (A05.Mode SpinBranch h) _ instDecidableEqProd
      (speciesChargeBoxSet h K B) ψ).mpr hBox
  have hcomm_ne : A02.commutator (speciesChargeBoxProjection h K B) (umklappOp h b gU) ψ ≠ 0 := by
    intro h0
    simp only [A02.commutator, LinearMap.sub_apply, Module.End.mul_apply, hPψ] at h0
    have hfix : speciesChargeBoxProjection h K B (umklappOp h b gU ψ) = umklappOp h b gU ψ :=
      sub_eq_zero.mp h0
    exact hnotmem ((@A03.projection_fixed_iff (A05.Mode SpinBranch h) _ instDecidableEqProd
      (speciesChargeBoxSet h K B) _).mp hfix)
  refine ⟨hnotmem, hcomm_ne, fun h0 => hcomm_ne (by rw [h0, LinearMap.zero_apply])⟩

/-- Theorem `thm:ch21-u-leakage` (inward / adjoint branch): symmetric leakage when the inward
Umklapp sum `∑_x O_U(x)† ψ ≠ 0` and its shifted target `Ns - ΔN` violates a charge bound `B_ν`. -/
theorem umklapp_charge_box_inward_leakage (h K : ℕ) (hh : 0 < h)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (gU : ℝ) (hg : gU ≠ 0)
    (B : SpinBranch → ℕ) (Ns : SpinBranch → ℤ)
    (ψ : A05.FockSpace SpinBranch h)
    (hBox : ψ ∈ speciesChargeBox h K B)
    (hSec : ψ ∈ chargeSector h Ns)
    (hIn : umklappBackwardSum h b ψ ≠ 0)
    (hExit : ∃ ν, (B ν : ℤ) < |umklappBackwardTarget Ns ν|) :
    umklappOp h b gU ψ ∉ speciesChargeBox h K B ∧
    A02.commutator (speciesChargeBoxProjection h K B) (umklappOp h b gU) ψ ≠ 0 ∧
    A02.commutator (speciesChargeBoxProjection h K B) (umklappOp h b gU) ≠ 0 := by
  have hFsec : umklappForwardSum h b ψ ∈ chargeSector h (umklappForwardTarget Ns) :=
    umklappForwardSum_maps_sector h b Ns ψ hSec
  have hBsec : umklappBackwardSum h b ψ ∈ chargeSector h (umklappBackwardTarget Ns) :=
    umklappBackwardSum_maps_sector h b Ns ψ hSec
  have hBF0 : inner ℂ (umklappBackwardSum h b ψ) (umklappForwardSum h b ψ) = 0 :=
    distinct_charge_sectors_orthogonal h (umklappBackwardTarget Ns) (umklappForwardTarget Ns)
      (umklapp_targets_distinct Ns).2.2.symm _ hBsec _ hFsec
  have hcne : (gU : ℂ) / (2 * (h : ℂ)) ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr hg)
      (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hh)))
  have hinner_ne : inner ℂ (umklappBackwardSum h b ψ) (umklappOp h b gU ψ) ≠ 0 := by
    rw [umklappOp_eq_smul_add_sums, LinearMap.smul_apply, LinearMap.add_apply, inner_smul_right,
      inner_add_right, hBF0, zero_add]
    exact mul_ne_zero hcne (fun h0 => hIn (inner_self_eq_zero.mp h0))
  have hnotmem : umklappOp h b gU ψ ∉ speciesChargeBox h K B := by
    intro hmem
    exact hinner_ne (chargeSector_orthogonal_speciesChargeBox h K B _ hExit _ hBsec _ hmem)
  have hPψ : speciesChargeBoxProjection h K B ψ = ψ :=
    (@A03.projection_fixed_iff (A05.Mode SpinBranch h) _ instDecidableEqProd
      (speciesChargeBoxSet h K B) ψ).mpr hBox
  have hcomm_ne : A02.commutator (speciesChargeBoxProjection h K B) (umklappOp h b gU) ψ ≠ 0 := by
    intro h0
    simp only [A02.commutator, LinearMap.sub_apply, Module.End.mul_apply, hPψ] at h0
    have hfix : speciesChargeBoxProjection h K B (umklappOp h b gU ψ) = umklappOp h b gU ψ :=
      sub_eq_zero.mp h0
    exact hnotmem ((@A03.projection_fixed_iff (A05.Mode SpinBranch h) _ instDecidableEqProd
      (speciesChargeBoxSet h K B) _).mp hfix)
  refine ⟨hnotmem, hcomm_ne, fun h0 => hcomm_ne (by rw [h0, LinearMap.zero_apply])⟩

/-- Basis-configuration corollary of `thm:ch21-u-leakage`: whenever a basis occupation `S` in the
box `ℬ_{K, B}` has a nonzero outward or inward Umklapp step exiting any upper/lower species charge
boundary `±B_ν`, the commutator `[P_{K, B}, H_U]` is nonzero. -/
theorem umklapp_charge_box_basis_leakage (h K : ℕ) (hh : 0 < h)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (gU : ℝ) (hg : gU ≠ 0)
    (B : SpinBranch → ℕ) (S : A05.Occupation SpinBranch h)
    (hS : S ∈ speciesChargeBoxSet h K B)
    (hStep :
      (umklappForwardSum h b (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S) ≠ 0 ∧
        ∃ ν, (B ν : ℤ) < |Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) + umklappDelta ν|) ∨
      (umklappBackwardSum h b (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S) ≠ 0 ∧
        ∃ ν, (B ν : ℤ) < |Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) - umklappDelta ν|)) :
    A02.commutator (speciesChargeBoxProjection h K B) (umklappOp h b gU) ≠ 0 := by
  let Ns : SpinBranch → ℤ := fun ν => Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν)
  have hBox : @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S ∈ speciesChargeBox h K B := by
    rw [speciesChargeBox, @A03.ket_mem_coordinate_space (A05.Mode SpinBranch h) _ instDecidableEqProd]
    exact hS
  have hSec : @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S ∈ chargeSector h Ns := by
    rw [chargeSector, @A03.ket_mem_coordinate_space (A05.Mode SpinBranch h) _ instDecidableEqProd]
    intro ν; rfl
  rcases hStep with ⟨hOut, hExit⟩ | ⟨hIn, hExit⟩
  · exact (umklapp_charge_box_outward_leakage h K hh b gU hg B Ns _ hBox hSec hOut hExit).2.2
  · exact (umklapp_charge_box_inward_leakage h K hh b gU hg B Ns _ hBox hSec hIn hExit).2.2

/-- Immediate zero-charge-box corollary: for every `h > 0`, `K : ℕ`, and `g_U ≠ 0`,
`[P_{K, 0}, H_U] ≠ 0` on the periodic lattice. -/
theorem umklapp_zero_box_commutator_ne_zero (h K : ℕ) (hh : 0 < h) (gU : ℝ) (hg : gU ≠ 0) :
    A02.commutator (speciesChargeBoxProjection h K (fun _ => 0)) (periodicUmklappOp h gU) ≠ 0 := by
  let b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h) := fun _ => Ch06Ext.periodicTwist (2 * h)
  have hBox : A05.groundKet h (fun _ => 0) ∈ speciesChargeBox h K (fun _ => 0) := by
    have hle : A05.jointBudget h (fun _ => 0) K ≤ speciesChargeBox h K (fun _ => 0) := by
      unfold A05.jointBudget Ch07.speciesBudget speciesChargeBox
      apply @A03.coordinate_space_mono (A05.Mode SpinBranch h) _ instDecidableEqProd
      intro S hS
      refine ⟨fun ν => by rw [hS.1 ν]; simp, hS.2⟩
    exact hle (A05.ground_mem_budget h hh (fun _ => 0) (zeroCharge_admissible h) K)
  have hSec : A05.groundKet h (fun _ => 0) ∈ chargeSector h (fun _ => 0) :=
    jointBudget_le_chargeSector h (fun _ => 0) 0
      (A05.ground_mem_budget h hh (fun _ => 0) (zeroCharge_admissible h) 0)
  have hOut : umklappForwardSum h b (A05.groundKet h (fun _ => 0)) ≠ 0 := by
    intro h0
    have hcoeff := umklapp_zero_charge_witness_coeff h hh 1
    have hB0 : inner ℂ (umklappZeroChargeWitness h hh)
        (umklappBackwardSum h b (A05.groundKet h (fun _ => 0))) = 0 :=
      distinct_charge_sectors_orthogonal h (umklappForwardTarget (fun _ => 0))
        (umklappBackwardTarget (fun _ => 0)) (umklapp_targets_distinct (fun _ => 0)).2.2
        _ (umklappZeroChargeWitness_mem_target_sector h hh)
        _ (umklappBackwardSum_maps_sector h b (fun _ => 0) _ hSec)
    change inner ℂ (umklappZeroChargeWitness h hh) (umklappOp h b 1 (A05.groundKet h (fun _ => 0))) = _
      at hcoeff
    rw [umklappOp_eq_smul_add_sums, LinearMap.smul_apply, LinearMap.add_apply, h0, zero_add,
      inner_smul_right, hB0, mul_zero] at hcoeff
    have hne : -((1 : ℂ) / ((2 * (h : ℂ)) ^ 2)) ≠ 0 := by
      have hhC : (h : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hh)
      exact neg_ne_zero.mpr (div_ne_zero one_ne_zero (pow_ne_zero 2 (mul_ne_zero two_ne_zero hhC)))
    exact hne hcoeff.symm
  have hExit : ∃ ν, ((0 : ℕ) : ℤ) < |umklappForwardTarget (fun _ => 0) ν| :=
    ⟨brLUp, by decide⟩
  exact (umklapp_charge_box_outward_leakage h K hh b gU hg (fun _ => 0) (fun _ => 0) _
    hBox hSec hOut hExit).2.2

end Bosonize.Ch21
