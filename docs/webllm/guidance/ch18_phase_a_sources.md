# CH18 Phase A — reviewed source guidance (2026-10-14)

Prepared by the orchestrator from a read-only literature/API analysis. **Proposals, not verified truths.** Every literature anchor refers to `References/references-transcripts/` (hub). Abbreviations: SEN = `senechal_1999/06_tomonaga_luttinger.md`, ML = `mattis_2013/mattis_luttinger_2013_ch01_the_luttinger_model_and_its_solution.md`, VDS10 = `von_delft_schoeller_1998/10_impurity_in_tll.md`, VDS4 = `von_delft_schoeller_1998/04_bosonic_fock_space.md`, GIA3 = `giamarchi_2004/03_ch03_luttinger_liquids_pdf084-113.md`, GIA22 = `giamarchi_2004/2.2_physical_properties_and_correlation_functions.md`.

## 0. Key fact: reuse frozen Core, do not re-invent

`Bosonize/Core/A07InteractionsAndBogoliubov.lean` (namespace `Bosonize.A07Interactions`, frozen) already provides:
`HyperbolicParams v1 v2` (fields `u c s`, `u_pos`, `c_pos`, `u_sq : u^2 = v1^2 - v2^2`, `hyperbolic_id : c^2 - s^2 = 1`, `match_v1 : v1 = u*(c^2+s^2)`, `match_v2 : v2 = 2*u*c*s`); `hyperbolic_params_exist` (∃ only); `bogoliubovCreator h m c s branches η = c•ρ_{m,η} + s•ρ_{-m,η̄}`; `bogoliubovAnnihilator … = c•ρ_{-m,η} + s•ρ_{m,η̄}`; `dressedModeNumber h m u c s`; `pairingMode h m v1 v2`; `hoppingMode`; `bogoliubov_creator_adjoint`; `bogoliubov_expansion_on_budget` (dressed = pairing + 2us²m on `A05.jointBudget` under `A06.branchMargins`); `bogoliubov_ccr_on_budget` (same-branch dressed CCR, only `c^2-s^2=1`); `raw_inter_eq_hopping`; `pairing_mode_ground_nonzero`; `hopping_mode_kills_ground`.
Also reuse: `A05.rho`, `A05.rho_adjoint`, `A05.rho_cross_commute` (global), `A05.rho_lowering_budget_zero`, `A05.groundKet`, `A05.ground_ne_zero`, `A05.admissible`, `A05.jointBudget`; `A06.Orientation`, `A06.Branches`, `A06.speciesOf`, `A06.marginAt`, `A06.branchMargins`, `A06.joint_signed_current_commutator`; `Ch16.excitedKet`, `Ch16.excited_ket_nonzero`, `Ch16.standardBranches`; `Ch17.v1Velocity vF g4 = vF + g4/(2π)`, `Ch17.v2Velocity g2 = g2/(2π)`, `Ch17.luttingerOscillatorOp` (prefactor `((2π:ℝ):ℂ)/((2h:ℕ):ℂ)`, sum over `Icc 1 M` of `pairingMode`), `Ch17.luttingerFermionChosenModel`, `Ch17.zeroModeEnergyScalar`, `Ch17.sugawaraMargin`, `Ch17.luttinger_hamiltonian_on_budget`, `Ch17.concrete_luttinger_witness`; A10 `energy_shell_discards_double_mode_one`, `sw_off_zero_implies_effective_exact`; `Ch02.finite_dimensional_no_go`.
Namespaces `Bosonize.A07Interactions` and `Bosonize.A07` (FiniteNormalOrdering) are different.

**Missing in Core (CH18 scope):** Ch17-connected sum over m, inverse transform, cross-branch dressed commutators, scalar consequences (g, tanh relation, closed-form vacuum constant, u<v1), constructive obstruction (Thm 18.8), witnesses with s ≠ 0.

## A. Claims ledger

| id | statement (finite form) | literature anchor | note | tier | finite? |
|---|---|---|---|---|---|
| ch18.c01 | real (c,s), c²−s²=1 ⇒ (c−s)(c+s)=1, c±s≠0 | SEN:95-98 (K=e^{2ξ}, φ = coshξ φ' + sinhξ φ̄'); VDS10:414-419 | Def 18.1 | T2 | yes |
| ch18.c02 | |v2|<v1 ⇒ ∃ u>0,c>0,s: u²=v1²−v2², c²−s²=1, v1=u(c²+s²), v2=2ucs (v1²>v2² alone insufficient) | GIA22:72-74; VDS10:366-369; ML:1114 (instability if violated) | Def 18.5 | T2 | yes (exists as ∃; add `Nonempty`) |
| ch18.c03 | tanh 2ξ = v2/v1, algebraic: v2(c²+s²) = v1(2cs) | none directly (ML (4.11) missing in transcript); ML:1112 indirect | (18.9) | T2 | yes, mark derived |
| ch18.c04 | g:=(c−s)², g⁻¹:=(c+s)²; g·g⁻¹=1; g·u=v1−v2; g⁻¹·u=v1+v2; g=√((v1−v2)/(v1+v2))>0; g<1 ⇔ v2>0 | GIA22:74,77; VDS10:368-369; SEN:35 | (18.10) | T2 | yes |
| ch18.c05 | u=√(v1²−v2²), v1=vF+g4/2π, v2=g2/2π (= Ch17 defs) | GIA22:66-74,77; SEN:37 | Def 18.5 | T2 | yes |
| ch18.c06 | v1>0, v2≠0 ⇒ u<v1 (⇔ s≠0 ⇔ v2≠0); NOT "u>vF" | ML:1112-1114 (plasmon energy lowered; g2-only model) | Cor 18.7 | T2 | yes |
| ch18.c07 | dressed modes C̃_η, Ã_η; Ã = C̃† for real c,s | SEN:101-106; VDS10:414-419; ML:1176-1180 | Def 18.2 | T2 | exists in A07 |
| ch18.c08 | inverse: ρ_{m,η} = c C̃_η − s Ã_η̄; ρ_{−m,η} = c Ã_η − s C̃_η̄ (global, only c²−s²=1) | SEN:104-105 (old-from-new, s ↔ −sinhξ) | Lemma 18.3 | T2 | yes (new) |
| ch18.c09 | same-branch dressed CCR on budget | VDS10:467-469; ML:1032-1034 | Thm 18.4 | T1 | exists (`bogoliubov_ccr_on_budget`) — cite |
| ch18.c10 | [Ã_η, C̃_η̄]=0 globally; [C̃_R,C̃_L]v=0 and [Ã_R,Ã_L]v=0 on budget (cs(∓m) cancel) | VDS10:467-469; ML:1035-1036 | gap in note | T1/T2 | yes (new) |
| ch18.c11 | per-mode: u(C̃_RÃ_R+C̃_LÃ_L)v = pairing_m v + 2us²m v | VDS10:389-398; GIA3:188 | (18.8) | T1 | exists — cite |
| ch18.c12 | `luttingerOscillatorOp … v` = (2π/2h)Σ_{m=1}^{M} dressedModeNumber v − ΔE v, ΔE=(2π/2h)Σ 2us²m | VDS10:400-411; ML:1081-1088 | Thm 18.6 | T1 | yes (new) |
| ch18.c13 | full chosen model: `luttingerFermionChosenModel … v` = dressed sum + ((zeroModeEnergyScalar − ΔE : ℝ):ℂ)•v (needs `admissible`, `sugawaraMargin`, `branchMargins`; neither margin implies the other) | as c12; SEN:22-37 | (18.11) | T1 | yes (new) |
| ch18.c14 | 2us² = v1−u ≥ 0; ΔE = (2π/L)(v1−u)M(M+1)/2 > 0 iff v2≠0 | ML:1114 (W_1 named; formula missing in transcript) | (18.11) | T2 | yes as operator constant; NOT as a ground-state energy |
| ch18.c15 | dressed quantum energy 2πum/L | SEN:61-62; GIA3:184-186; ML:1112 | 18.3 | T2 | defer (only an equation-of-motion form is provable) |
| ch18.c16 | obstruction: no common bare/dressed vacuum; constructive: Ã_η(groundKet) = s•Ch16.excitedKet … η̄ m, ≠0 when s≠0 under marginAt | ML:1146 (new ground state ≠ Ψ_0, infinite model) | Thm 18.8 | T1 | yes (new) |
| ch18.c17 | finite caveats: no unitary implementer / global CCR (`Ch02.finite_dimensional_no_go`); chosen pairing model ≠ raw finite g2 (hopping, eigenvalues v1±v2) | ML:1022-1027; GIA3:188 | note L44,94,98 | T2 | caveat only |
| ch18.c18 | witness (v1,v2,u,c,s)=(17,15,8,5/4,3/4): c²−s²=1, u²=64, u(c²+s²)=17, 2ucs=15, g=1/4, 2us²=9=v1−u; vF=1, g4=32π, g2=30π; carrier h=8, M=2, K=2, Ns=0, standardBranches | internal | F2 | T2 | yes (norm_num) |
| ch18.c19 | energy-shell vs mode decimation, block-diagonal SW | none | Thm 18.9 | T2 | exists in A10 — cite; "RG fixed line" is interpretation only |

## B. Convention flags (must respect)
1. **Orientation:** project modes are "computational" (ρ_{m,ν}, m>0 raises on both branches; [ρ_{−m},ρ_m]=+m). The left branch is index-reflected relative to ML/SEN physical labels (VDS4:135-143 matches the project).
2. **Mixing:** (m,R) with (−m,L): C̃_R = cC_R + sA_L, C̃_L = cC_L + sA_R (consistent with SEN:104 structure).
3. **Sign of s:** project = NEW from OLD (tilde = c·old + s·old†); SEN gives OLD from NEW, so ξ_note = −ξ_SEN; repulsive v2>0 ⇒ s>0, g<1. Flip ξ when porting SEN formulas.
4. **VDS10:397 minus sign** on the pairing term is an i-phase artifact of VDS4 conventions; the project `pairingMode` has +v2. Do not copy the minus sign.
5. **Couplings:** Ch17 matches GIA22 exactly (v1=vF+g4/2π, v2=g2/2π, L=2h). VDS/SEN differ by 2π factors.
6. **Never name the Luttinger parameter `K`** (K is the energy budget). Use `luttingerG`.
7. **Normal-ordering constant is convention-dependent**; the only formal claim is the exact operator identity under the Ch17/A07 ordering.
8. **Zero modes:** CH18 transforms only m≥1; keep `Ch17.zeroModeEnergyScalar` (no zero-mode rotation).
9. **Physical g2 vs finite raw g2:** CH18 diagonalizes the chosen pairing model, not the raw finite density-density term (`raw_inter_eq_hopping`).
10. Transcript defects (do not cite these equations): GIA22:67 garbled; ML (4.7)–(4.13) missing (page jump ML:1090-1092); ML:1401, 1407, 1413 garbled exponents.

## C. Review of the user's earlier Gemini draft (`notes/draft-lean-code/ch18-bogoliubov-draft-gemini-pro.md`, untracked, unverified)
- **Reusable:** `HyperbolicPair` with `mul_eq_one`, `c_sub_s_ne_zero`, `c_add_s_ne_zero` (keep the name `HyperbolicPair` with fields `c`, `s`: a later A08 draft imports `Bosonize.Core.Ch18Bogoliubov` and uses `Ch18.HyperbolicPair` `.c`/`.s`; rename the proof field to `hyperbolic_id`); closed-form A=√((v1+v2)/u), B=√((v1−v2)/u), c=(A+B)/2, s=(A−B)/2 (AB=1; algebra checked); g identities; `u_lt_v1`; inverse transforms; minimal no-common-vacuum lemma.
- **Rejected patterns:** `import Mathlib` (verifier allows only `import Bosonize`/`Bosonize.Core.X`); `local notation` (not an allowed command); an abstract `rho` variable family never tied to `A05.rho`; extra `[DecidableEq σ]`; duplicates of A07 (`dressedRho*`, `pairingSummand`, `kac_moody_of_relations`, `diag_summand_of_relations`); a local stand-in `pairingHamiltonian` instead of `Ch17.luttingerOscillatorOp`; free `Llen` (Llen=0 trivializes statements; tie to 2h); arbitrary `Ezero` operator.
- **F2 (vacuity) defects:** `CurrentCCRBridge` assumed as a hypothesis with arbitrary `Margin` (vacuous with `Margin := False`) — derive CCR from Core instead; only witness has s=0; SW block-diagonal statement trivially true (distributivity; hypotheses unused).
- **F1 (over-claim):** "exact diagonalization" is an operator identity on budget vectors for the chosen pairing model only — not a spectral statement, not a dressed vacuum, not the raw finite g2 interaction. State this caveat in docstrings.

### Reusable excerpts (verbatim from the draft; adapt names/fields to the Core API above)

```text
structure HyperbolicPair where
  c : ℝ
  s : ℝ
  h : c ^ 2 - s ^ 2 = 1

namespace HyperbolicPair
variable (hp : HyperbolicPair)

/-- Auxiliary identity `(c - s)(c + s) = 1`. -/
lemma mul_eq_one : (hp.c - hp.s) * (hp.c + hp.s) = 1 := by
  linear_combination hp.h

/-- The identity (18.1) cast to `ℂ`. -/
lemma hC : (hp.c : ℂ) ^ 2 - (hp.s : ℂ) ^ 2 = 1 := by
  exact_mod_cast hp.h

/-- Product form of (18.1) in `ℂ`. -/
lemma hC' : (hp.c : ℂ) * hp.c - hp.s * hp.s = 1 := by
  linear_combination hp.hC

lemma c_sub_s_ne_zero : hp.c - hp.s ≠ 0 := by
  intro h0
  have h1 := hp.mul_eq_one
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

lemma c_add_s_ne_zero : hp.c + hp.s ≠ 0 := by
  intro h0
  have h1 := hp.mul_eq_one
  rw [h0, mul_zero] at h1
  exact zero_ne_one h1

/-- Trivial witness (no interaction). -/
def trivial : HyperbolicPair := ⟨1, 0, by norm_num⟩

end HyperbolicPair
```

```text
/-! ## 2. Real-analysis layer for Definition 18.5 (closed-form witnesses) -/
section Velocities
variable {v₁ v₂ : ℝ}

lemma stab_plus (hstab : |v₂| < v₁) : 0 < v₁ + v₂ := by
  have := neg_abs_le v₂
  linarith

lemma stab_minus (hstab : |v₂| < v₁) : 0 < v₁ - v₂ := by
  have := le_abs_self v₂
  linarith

lemma stab_sq (hstab : |v₂| < v₁) : 0 < v₁ ^ 2 - v₂ ^ 2 := by
  have e : v₁ ^ 2 - v₂ ^ 2 = (v₁ + v₂) * (v₁ - v₂) := by ring
  rw [e]
  exact mul_pos (stab_plus hstab) (stab_minus hstab)

/-- `u = √(v₁² - v₂²)`. -/
def uOf (v₁ v₂ : ℝ) : ℝ := Real.sqrt (v₁ ^ 2 - v₂ ^ 2)

/-- `A = √((v₁ + v₂)/u)`; plays the role of `c + s`. -/
def aOf (v₁ v₂ : ℝ) : ℝ := Real.sqrt ((v₁ + v₂) / uOf v₁ v₂)

/-- `B = √((v₁ - v₂)/u)`; plays the role of `c - s`. -/
def bOf (v₁ v₂ : ℝ) : ℝ := Real.sqrt ((v₁ - v₂) / uOf v₁ v₂)

lemma uOf_pos (hstab : |v₂| < v₁) : 0 < uOf v₁ v₂ :=
  Real.sqrt_pos.mpr (stab_sq hstab)

lemma uOf_sq (hstab : |v₂| < v₁) : uOf v₁ v₂ ^ 2 = v₁ ^ 2 - v₂ ^ 2 :=
  Real.sq_sqrt (stab_sq hstab).le

lemma aOf_pos (hstab : |v₂| < v₁) : 0 < aOf v₁ v₂ :=
  Real.sqrt_pos.mpr (div_pos (stab_plus hstab) (uOf_pos hstab))

lemma bOf_pos (hstab : |v₂| < v₁) : 0 < bOf v₁ v₂ :=
  Real.sqrt_pos.mpr (div_pos (stab_minus hstab) (uOf_pos hstab))

lemma aOf_sq_mul (hstab : |v₂| < v₁) : aOf v₁ v₂ ^ 2 * uOf v₁ v₂ = v₁ + v₂ := by
  have hu : uOf v₁ v₂ ≠ 0 := (uOf_pos hstab).ne'
  unfold aOf
  rw [Real.sq_sqrt (div_pos (stab_plus hstab) (uOf_pos hstab)).le]
  field_simp

lemma bOf_sq_mul (hstab : |v₂| < v₁) : bOf v₁ v₂ ^ 2 * uOf v₁ v₂ = v₁ - v₂ := by
  have hu : uOf v₁ v₂ ≠ 0 := (uOf_pos hstab).ne'
  unfold bOf
  rw [Real.sq_sqrt (div_pos (stab_minus hstab) (uOf_pos hstab)).le]
  field_simp

/-- `A * B = 1`, the key identity that avoids any sign case-split on `v₂`. -/
lemma aOf_mul_bOf (hstab : |v₂| < v₁) : aOf v₁ v₂ * bOf v₁ v₂ = 1 := by
  have hu : uOf v₁ v₂ ≠ 0 := (uOf_pos hstab).ne'
  have h1 : (aOf v₁ v₂ * bOf v₁ v₂) ^ 2 * uOf v₁ v₂ ^ 2 = 1 * uOf v₁ v₂ ^ 2 := by
    calc (aOf v₁ v₂ * bOf v₁ v₂) ^ 2 * uOf v₁ v₂ ^ 2
        = (aOf v₁ v₂ ^ 2 * uOf v₁ v₂) * (bOf v₁ v₂ ^ 2 * uOf v₁ v₂) := by ring
      _ = (v₁ + v₂) * (v₁ - v₂) := by rw [aOf_sq_mul hstab, bOf_sq_mul hstab]
      _ = uOf v₁ v₂ ^ 2 := by rw [uOf_sq hstab]; ring
      _ = 1 * uOf v₁ v₂ ^ 2 := (one_mul _).symm
  have h2 : (aOf v₁ v₂ * bOf v₁ v₂) ^ 2 = 1 := mul_right_cancel₀ (pow_ne_zero 2 hu) h1
  have hpos : 0 < aOf v₁ v₂ * bOf v₁ v₂ := mul_pos (aOf_pos hstab) (bOf_pos hstab)
  have h3 : (aOf v₁ v₂ * bOf v₁ v₂ - 1) * (aOf v₁ v₂ * bOf v₁ v₂ + 1) = 0 := by
    linear_combination h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · linarith
  · linarith

end Velocities


/-! ## 3. Definition 18.5 — the `LuttingerParams` record -/

/-- Definition 18.5. Parameters matched to the pairing Hamiltonian with
`v₁ = v_F + g₄/2π`, `v₂ = g₂/2π`. Extends `HyperbolicPair`, so `c s` and `c² - s² = 1`
are inherited. Fields encode (18.9) (`v1_eq`, `v2_eq`) and (18.10) (`g`, `ginv`). -/
structure LuttingerParams (v₁ v₂ : ℝ) extends HyperbolicPair where
  stab : |v₂| < v₁
  u : ℝ
  u_pos : 0 < u
  u_eq : u = Real.sqrt (v₁ ^ 2 - v₂ ^ 2)
  v1_eq : u * (c ^ 2 + s ^ 2) = v₁
  v2_eq : u * (2 * c * s) = v₂
  g : ℝ
  ginv : ℝ
  g_eq : g = (c - s) ^ 2
  ginv_eq : ginv = (c + s) ^ 2
  g_mul : g * ginv = 1

/-- Closed-form witnesses: `c = (A+B)/2`, `s = (A-B)/2`, so `c - s = B`, `c + s = A`. -/
def LuttingerParams.ofVelocities (v₁ v₂ : ℝ) (hstab : |v₂| < v₁) :
    LuttingerParams v₁ v₂ where
  c := (aOf v₁ v₂ + bOf v₁ v₂) / 2
  s := (aOf v₁ v₂ - bOf v₁ v₂) / 2
  h := by linear_combination aOf_mul_bOf hstab
  stab := hstab
  u := uOf v₁ v₂
  u_pos := uOf_pos hstab
  u_eq := rfl
  v1_eq := by
    linear_combination (1 / 2 : ℝ) * aOf_sq_mul hstab + (1 / 2 : ℝ) * bOf_sq_mul hstab
  v2_eq := by
    linear_combination (1 / 2 : ℝ) * aOf_sq_mul hstab - (1 / 2 : ℝ) * bOf_sq_mul hstab
  g := ((aOf v₁ v₂ + bOf v₁ v₂) / 2 - (aOf v₁ v₂ - bOf v₁ v₂) / 2) ^ 2
  ginv := ((aOf v₁ v₂ + bOf v₁ v₂) / 2 + (aOf v₁ v₂ - bOf v₁ v₂) / 2) ^ 2
  g_eq := rfl
  ginv_eq := rfl
  g_mul := by linear_combination (aOf v₁ v₂ * bOf v₁ v₂ + 1) * aOf_mul_bOf hstab
```

```text
theorem rho_R_inverse (hp : HyperbolicPair) (m : ℕ) :
    rho .right (m : ℤ)
      = (hp.c : ℂ) • dressedRhoR rho hp m - (hp.s : ℂ) • dressedRhoNegL rho hp m := by
  refine (smul_one_aux hp _).trans ?_
  simp only [dressedRhoR, dressedRhoNegL]
  module

/-- `ρ_{-m,L} = c ρ̃_{-m,L} - s ρ̃_{m,R}`. -/
theorem rho_L_neg_inverse (hp : HyperbolicPair) (m : ℕ) :
    rho .left (-(m : ℤ))
      = (hp.c : ℂ) • dressedRhoNegL rho hp m - (hp.s : ℂ) • dressedRhoR rho hp m := by
  refine (smul_one_aux hp _).trans ?_
  simp only [dressedRhoR, dressedRhoNegL]
  module

/-- `ρ_{-m,R} = c ρ̃_{-m,R} - s ρ̃_{m,L}`. -/
theorem rho_R_neg_inverse (hp : HyperbolicPair) (m : ℕ) :
    rho .right (-(m : ℤ))
      = (hp.c : ℂ) • dressedRhoNegR rho hp m - (hp.s : ℂ) • dressedRhoL rho hp m := by
  refine (smul_one_aux hp _).trans ?_
  simp only [dressedRhoNegR, dressedRhoL]
  module

/-- `ρ_{m,L} = c ρ̃_{m,L} - s ρ̃_{-m,R}`. -/
theorem rho_L_inverse (hp : HyperbolicPair) (m : ℕ) :
    rho .left (m : ℤ)
      = (hp.c : ℂ) • dressedRhoL rho hp m - (hp.s : ℂ) • dressedRhoNegR rho hp m := by
  refine (smul_one_aux hp _).trans ?_
  simp only [dressedRhoNegR, dressedRhoL]
  module
```

```text
theorem no_bare_dressed_vacuum_minimal (hp : HyperbolicPair) (hs : hp.s ≠ 0)
    {m : ℕ} (hm : 1 ≤ m) {ψ : Fock} (hψ : ψ ≠ 0)
    (hLL : A02.commutator (rho .left (-(m : ℤ))) (rho .left (m : ℤ)) ψ = (m : ℂ) • ψ)
    (hbareR : (rho .right (-(m : ℤ))) ψ = 0)
    (hbareL : (rho .left (-(m : ℤ))) ψ = 0)
    (hdressR : (dressedRhoNegR rho hp m) ψ = 0) : False := by
  have h1 : (hp.s : ℂ) • (rho .left (m : ℤ)) ψ = 0 := by
    have h2 := hdressR
    simp only [dressedRhoNegR, LinearMap.add_apply, LinearMap.smul_apply, hbareR,
      smul_zero, zero_add] at h2
    exact h2
  have h2 : (rho .left (m : ℤ)) ψ = 0 :=
    (smul_eq_zero.mp h1).resolve_left (Complex.ofReal_ne_zero.mpr hs)
  have h3 : A02.commutator (rho .left (-(m : ℤ))) (rho .left (m : ℤ)) ψ = 0 := by
    simp only [A02.commutator, LinearMap.sub_apply, mul_apply_eq, h2, hbareL, map_zero,
      sub_self]
  rw [h3] at hLL
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact hψ ((smul_eq_zero.mp hLL.symm).resolve_left hm0)
```

## D. Recommended Phase A scope

Module `BosonizeStubs/Ch18Bogoliubov.lean`, namespace `Bosonize.Ch18` (final Core path `Bosonize/Core/Ch18Bogoliubov.lean`). Imports: `Bosonize.Core.A07InteractionsAndBogoliubov`, `Bosonize.Core.Ch16FieldHamiltonian`, `Bosonize.Core.Ch17LuttingerModels` (A10 only if cited). Variables `{σ : Type*} [Fintype σ] [LinearOrder σ]`.

**Data (complete, no sorry):** `structure HyperbolicPair` (c s : ℝ, hyperbolic_id); `HyperbolicPair.ofParams (hp : A07Interactions.HyperbolicParams v1 v2)`; `luttingerG p := (p.c - p.s)^2`, `luttingerGInv p := (p.c + p.s)^2`; `vacuumShiftScalar h M u s := (2π/((2h:ℕ):ℝ)) * Σ_{m∈Icc 1 M} 2us²m`; `dressedOscillatorOp h M u c s branches := ((2π:ℝ):ℂ)/((2h:ℕ):ℂ) • Σ_{m∈Icc 1 M} dressedModeNumber h m u c s branches`; `concreteParams : A07Interactions.HyperbolicParams 17 15 := {u := 8, c := 5/4, s := 3/4, …}` with each field proved by `norm_num` (never `Classical.choice` of a sorried statement).

**Theorem contracts (each `:= by sorry`):** scalar 1–8 (sub_mul_add, g·g⁻¹=1 & g>0, g·u = v1−v2 & g⁻¹·u = v1+v2, g = √((v1−v2)/(v1+v2)), tanh relation, 2us² = v1−u, s≠0 ↔ v2≠0 & u<v1 for v2≠0, `Nonempty (HyperbolicParams v1 v2)` from |v2|<v1); operator 9–16 (inverse transforms; global opposite-branch commutation; same-mode cross-branch creators/annihilators commute on budget; `luttinger_oscillator_dressed_on_budget` with `hv1 : v1 = Ch17.v1Velocity vF g4`, `hv2 : v2 = Ch17.v2Velocity g2`; `luttinger_hamiltonian_dressed_on_budget` (18.11) with `admissible`, `sugawaraMargin`, `branchMargins`; `dressed_annihilator_ground` = s • excitedKet (constructive); its `≠ 0` version under `s ≠ 0` and `marginAt`; `no_common_bare_dressed_vacuum`); witness 17 `concrete_bogoliubov_witness` (velocities 17/15 from vF=1, g4=32π, g2=30π; margins at h=8, M=2, K=2, Ns=0, standardBranches; s≠0; dressed annihilator on ground ≠ 0; dressedModeNumber on ground ≠ 0; vacuumShiftScalar 8 2 8 (3/4) = 27π/8 ≠ 0).
Do not restate `bogoliubov_ccr_on_budget` / `bogoliubov_expansion_on_budget`; cite them.

**Defer / caveat only:** spectrum and dressed vacuum energy; unitary implementer e^{iS}; zero-mode rotation; momentum-dependent couplings; correlation exponents; "LL as RG fixed line"; Thm 18.9(1)-(2) (cite A10); physical-g2 identification.
