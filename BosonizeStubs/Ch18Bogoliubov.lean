import Bosonize.Core.A07InteractionsAndBogoliubov
import Bosonize.Core.Ch16FieldHamiltonian
import Bosonize.Core.Ch17LuttingerModels

namespace Bosonize.Ch18

open scoped BigOperators

section Scalars

/-- Definition 18.1 in a scalar wrapper that fixes the sign choice
`c^2 - s^2 = 1` explicitly. -/
structure HyperbolicPair where
  c : ℝ
  s : ℝ
  hyperbolic_id : c ^ 2 - s ^ 2 = 1

def HyperbolicPair.ofParams {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) : HyperbolicPair where
  c := hp.c
  s := hp.s
  hyperbolic_id := hp.hyperbolic_id

def luttingerG (hp : HyperbolicPair) : ℝ :=
  (hp.c - hp.s) ^ 2

def luttingerGInv (hp : HyperbolicPair) : ℝ :=
  (hp.c + hp.s) ^ 2

abbrev LuttingerParams (v1 v2 : ℝ) := Bosonize.A07Interactions.HyperbolicParams v1 v2

def LuttingerParams.toHyperbolicPair {v1 v2 : ℝ} (lp : LuttingerParams v1 v2) :
    HyperbolicPair :=
  HyperbolicPair.ofParams lp

/-- Finite normal-ordering shift with the chapter prefactor tied to `L = 2h`.
This is only the scalar correction for the chosen pairing model, not a dressed
vacuum energy theorem. -/
noncomputable def vacuumShiftScalar (h M : ℕ) (u s : ℝ) : ℝ :=
  ((2 * Real.pi) / ((2 * h : ℕ) : ℝ)) *
    ∑ m ∈ Finset.Icc 1 M, (2 * u * s ^ 2 * (m : ℝ))

def concreteV1 : ℝ := 17

def concreteV2 : ℝ := 15

noncomputable def concreteVF : ℝ := 1

noncomputable def concreteG4 : ℝ := 32 * Real.pi

noncomputable def concreteG2 : ℝ := 30 * Real.pi

def concreteCarrierH : ℕ := 8

def concreteCutoff : ℕ := 2

def concreteBudget : ℕ := 2

def concreteMode : ℕ := 2

def concreteNs : Fin 2 → ℤ := fun _ => 0

def concreteBranches : Bosonize.A06.Branches (Fin 2) :=
  Bosonize.Ch16.standardBranches

/-- Explicit scalar witness required by the Phase A contract:
`(v1,v2,u,c,s) = (17,15,8,5/4,3/4)`, hence `s ≠ 0`. -/
noncomputable def concreteParams : Bosonize.A07Interactions.HyperbolicParams concreteV1 concreteV2 where
  u := 8
  c := 5 / 4
  s := 3 / 4
  u_pos := by
    norm_num
  c_pos := by
    norm_num
  u_sq := by
    norm_num [concreteV1, concreteV2]
  hyperbolic_id := by
    norm_num
  match_v1 := by
    norm_num [concreteV1]
  match_v2 := by
    norm_num [concreteV2]

noncomputable def concretePair : HyperbolicPair :=
  HyperbolicPair.ofParams concreteParams

lemma HyperbolicPair.mul_eq_one (hp : HyperbolicPair) :
    (hp.c - hp.s) * (hp.c + hp.s) = 1 := by
  nlinarith [hp.hyperbolic_id]

lemma HyperbolicPair.c_sub_s_ne_zero (hp : HyperbolicPair) :
    hp.c - hp.s ≠ 0 := by
  intro h
  have hid := hp.hyperbolic_id
  have hcs : hp.c = hp.s := by linarith
  rw [hcs, sub_self] at hid
  linarith

lemma HyperbolicPair.c_add_s_ne_zero (hp : HyperbolicPair) :
    hp.c + hp.s ≠ 0 := by
  intro h
  have h1 : hp.c ^ 2 - hp.s ^ 2 = 1 := hp.hyperbolic_id
  have h2 : hp.c ^ 2 - hp.s ^ 2 = (hp.c - hp.s) * (hp.c + hp.s) := by ring
  rw [h2, h, mul_zero] at h1
  norm_num at h1

/-- Carrier-independent Lemma 18.3 for reuse on other carriers. -/

theorem HyperbolicPair.inverse_combination {E : Type*} [AddCommGroup E] [Module ℂ E]
    (hp : HyperbolicPair) (X Y : E) :
    (hp.c : ℂ) • ((hp.c : ℂ) • X + (hp.s : ℂ) • Y) -
      (hp.s : ℂ) • ((hp.c : ℂ) • Y + (hp.s : ℂ) • X) = X := by
  have hsq : ((hp.c : ℂ) * (hp.c : ℂ) - (hp.s : ℂ) * (hp.s : ℂ)) = 1 := by
    simpa [pow_two] using congrArg (fun r : ℝ => (r : ℂ)) hp.hyperbolic_id
  have hX : (hp.c : ℂ) • ((hp.c : ℂ) • X) - (hp.s : ℂ) • ((hp.s : ℂ) • X) = X := by
    rw [← mul_smul, ← mul_smul, ← sub_smul]
    rw [hsq]
    simp
  have hY : (hp.c : ℂ) • ((hp.s : ℂ) • Y) - (hp.s : ℂ) • ((hp.c : ℂ) • Y) = 0 := by
    rw [← mul_smul, ← mul_smul, ← sub_smul]
    have hcoeff : ((hp.c : ℂ) * (hp.s : ℂ) - (hp.s : ℂ) * (hp.c : ℂ)) = 0 := by
      ring
    rw [hcoeff]
    simp
  calc
    (hp.c : ℂ) • ((hp.c : ℂ) • X + (hp.s : ℂ) • Y) -
        (hp.s : ℂ) • ((hp.c : ℂ) • Y + (hp.s : ℂ) • X)
      = ((hp.c : ℂ) • ((hp.c : ℂ) • X) - (hp.s : ℂ) • ((hp.s : ℂ) • X)) +
          ((hp.c : ℂ) • ((hp.s : ℂ) • Y) - (hp.s : ℂ) • ((hp.c : ℂ) • Y)) := by
          rw [smul_add, smul_add, sub_eq_add_neg, neg_add]
          abel
    _ = X + 0 := by rw [hX, hY]
    _ = X := by simp

theorem hyperbolic_params_nonempty (v1 v2 : ℝ) (hstab : |v2| < v1) :
    Nonempty (Bosonize.A07Interactions.HyperbolicParams v1 v2) := by
  rcases Bosonize.A07Interactions.hyperbolic_params_exist v1 v2 hstab with ⟨u, c, s, hu, hu2, hid, hv1, hv2⟩
  by_cases hc : 0 < c
  · exact ⟨⟨u, c, s, hu, hc, hu2, hid, hv1, hv2⟩⟩
  · have h_c_ne_zero : c ≠ 0 := by
      intro h
      have : 0 ^ 2 - s ^ 2 = 1 := by rw [← h, hid]
      linarith [sq_nonneg s]
    have hc_pos : 0 < -c := lt_of_le_of_ne (by linarith) (by intro h; apply h_c_ne_zero; linarith)
    exact ⟨⟨u, -c, -s, hu, hc_pos, hu2, by linarith, by linarith, by linarith⟩⟩

theorem tanh_relation_of_params {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) :
    v2 * (hp.c ^ 2 + hp.s ^ 2) = v1 * (2 * hp.c * hp.s) := by
  have h2 := congrArg (fun x : ℝ => x * (hp.c ^ 2 + hp.s ^ 2)) hp.match_v2
  have h1 := congrArg (fun x : ℝ => x * (2 * hp.c * hp.s)) hp.match_v1
  calc
    v2 * (hp.c ^ 2 + hp.s ^ 2) = (2 * hp.u * hp.c * hp.s) * (hp.c ^ 2 + hp.s ^ 2) := h2
    _ = (hp.u * (hp.c ^ 2 + hp.s ^ 2)) * (2 * hp.c * hp.s) := by ring
    _ = v1 * (2 * hp.c * hp.s) := h1.symm

theorem luttingerG_mul_inv (hp : HyperbolicPair) :
    luttingerG hp * luttingerGInv hp = 1 := by
  have hmul : (hp.c - hp.s) * (hp.c + hp.s) = 1 := by
    calc
      (hp.c - hp.s) * (hp.c + hp.s) = hp.c ^ 2 - hp.s ^ 2 := by ring
      _ = 1 := hp.hyperbolic_id
  calc
    luttingerG hp * luttingerGInv hp = ((hp.c - hp.s) * (hp.c + hp.s)) ^ 2 := by
      unfold luttingerG luttingerGInv
      ring
    _ = 1 := by
      rw [hmul]
      norm_num

theorem luttingerGInv_eq_inv (hp : HyperbolicPair) :
    luttingerGInv hp = (luttingerG hp)⁻¹ := by
  have hprod : (hp.c - hp.s) * (hp.c + hp.s) = 1 := by
    calc
      (hp.c - hp.s) * (hp.c + hp.s) = hp.c ^ 2 - hp.s ^ 2 := by ring
      _ = 1 := hp.hyperbolic_id
  have hmul : luttingerG hp * luttingerGInv hp = 1 := by
    dsimp [luttingerG, luttingerGInv]
    calc
      (hp.c - hp.s) ^ 2 * (hp.c + hp.s) ^ 2 = ((hp.c - hp.s) * (hp.c + hp.s)) ^ 2 := by ring
      _ = 1 := by rw [hprod]; norm_num
  have hmul' : luttingerGInv hp * luttingerG hp = 1 := by
    simpa [mul_comm] using hmul
  have hnonzero : luttingerG hp ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hmul
    exact zero_ne_one hmul
  apply mul_right_cancel₀ hnonzero
  calc
    luttingerGInv hp * luttingerG hp = 1 := hmul'
    _ = (luttingerG hp)⁻¹ * luttingerG hp := by
      symm
      exact inv_mul_cancel₀ hnonzero

theorem luttingerG_mul_u_of_params {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) :
    luttingerG (HyperbolicPair.ofParams hp) * hp.u = v1 - v2 := by
  change (hp.c - hp.s) ^ 2 * hp.u = v1 - v2
  nlinarith [hp.match_v1, hp.match_v2]

theorem luttingerGInv_mul_u_of_params {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) :
    luttingerGInv (HyperbolicPair.ofParams hp) * hp.u = v1 + v2 := by
  simp [luttingerGInv, HyperbolicPair.ofParams, hp.match_v1, hp.match_v2]
  ring

theorem luttingerG_eq_sqrt_of_params {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) :
    luttingerG (HyperbolicPair.ofParams hp) = Real.sqrt ((v1 - v2) / (v1 + v2)) := by
  dsimp [luttingerG, HyperbolicPair.ofParams]
  have hid : hp.c^2 - hp.s^2 = 1 := hp.hyperbolic_id
  have hu_pos : 0 < hp.u := hp.u_pos
  have num_eq : v1 - v2 = hp.u * (hp.c - hp.s)^2 := by
    calc v1 - v2 = hp.u * (hp.c^2 + hp.s^2) - 2 * hp.u * hp.c * hp.s := by
          exact congrArg₂ (fun x y => x - y) hp.match_v1 hp.match_v2
      _ = hp.u * (hp.c^2 + hp.s^2 - 2 * hp.c * hp.s) := by ring
      _ = hp.u * (hp.c - hp.s)^2 := by ring
  have den_eq : v1 + v2 = hp.u * (hp.c + hp.s)^2 := by
    calc v1 + v2 = hp.u * (hp.c^2 + hp.s^2) + 2 * hp.u * hp.c * hp.s := by
          exact congrArg₂ (fun x y => x + y) hp.match_v1 hp.match_v2
      _ = hp.u * (hp.c^2 + hp.s^2 + 2 * hp.c * hp.s) := by ring
      _ = hp.u * (hp.c + hp.s)^2 := by ring
  have frac_eq : (v1 - v2) / (v1 + v2) = (hp.c - hp.s)^2 / (hp.c + hp.s)^2 := by
    rw [num_eq, den_eq]
    rw [mul_div_mul_left _ _ (ne_of_gt hu_pos)]
  rw [frac_eq]
  have H_sq_div : (hp.c - hp.s)^2 / (hp.c + hp.s)^2 = ((hp.c - hp.s)^2)^2 := by
    calc (hp.c - hp.s)^2 / (hp.c + hp.s)^2 = (hp.c - hp.s)^2 * (hp.c - hp.s)^2 / ((hp.c + hp.s)^2 * (hp.c - hp.s)^2) := by
          have diff_sub_ne_zero : hp.c - hp.s ≠ 0 := by
            intro hc
            have hc2 : (hp.c + hp.s) * (hp.c - hp.s) = 0 := by rw [hc, mul_zero]
            have hdiff : (hp.c + hp.s) * (hp.c - hp.s) = hp.c^2 - hp.s^2 := by ring
            rw [hdiff, hid] at hc2
            exact zero_ne_one hc2.symm
          have diff_sq_ne_zero : (hp.c - hp.s)^2 ≠ 0 := pow_ne_zero 2 diff_sub_ne_zero
          rw [mul_div_mul_right _ _ diff_sq_ne_zero]
      _ = ((hp.c - hp.s)^2)^2 / ((hp.c + hp.s)*(hp.c - hp.s))^2 := by ring
      _ = ((hp.c - hp.s)^2)^2 / (hp.c^2 - hp.s^2)^2 := by ring
      _ = ((hp.c - hp.s)^2)^2 / 1^2 := by rw [hid]
      _ = ((hp.c - hp.s)^2)^2 := by ring
  rw [H_sq_div]
  exact (Real.sqrt_sq (sq_nonneg _)).symm

theorem luttingerG_pos_of_params {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) :
    0 < luttingerG (HyperbolicPair.ofParams hp) := by
  dsimp [luttingerG]
  apply sq_pos_of_ne_zero
  intro h
  have hcs : hp.c = hp.s := sub_eq_zero.mp h
  have h01 : (0 : ℝ) = 1 := by
    simpa [hcs] using hp.hyperbolic_id
  linarith

theorem luttingerGInv_pos_of_params {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) :
    0 < luttingerGInv (HyperbolicPair.ofParams hp) := by
  dsimp [luttingerGInv, HyperbolicPair.ofParams]
  have h_ne_zero : hp.c + hp.s ≠ 0 := by
    intro h
    have h1 : (hp.c - hp.s) * (hp.c + hp.s) = 1 := by
      calc (hp.c - hp.s) * (hp.c + hp.s) = hp.c ^ 2 - hp.s ^ 2 := by ring
      _ = 1 := hp.hyperbolic_id
    rw [h, mul_zero] at h1
    revert h1
    exact one_ne_zero.symm
  exact sq_pos_of_ne_zero h_ne_zero

theorem hyperbolic_coeff_eq_luttinger (hp : HyperbolicPair) :
    hp.c ^ 2 + hp.s ^ 2 = (luttingerG hp + (luttingerG hp)⁻¹) / 2 := by
  rw [← luttingerGInv_eq_inv hp]
  dsimp [luttingerG, luttingerGInv]
  ring

theorem v2_eq_zero_iff_s_eq_zero {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) :
    v2 = 0 ↔ hp.s = 0 := by
  constructor
  · intro hv2
    have hmul : 2 * hp.u * hp.c * hp.s = 0 := by
      simpa [hp.match_v2] using hv2
    have hfac_pos : 0 < 2 * hp.u * hp.c := by
      have htwo : (0 : ℝ) < 2 := by norm_num
      have hu : 0 < 2 * hp.u := mul_pos htwo hp.u_pos
      exact mul_pos hu hp.c_pos
    have hfac : 2 * hp.u * hp.c ≠ 0 := ne_of_gt hfac_pos
    rcases mul_eq_zero.mp hmul with hleft | hs
    · exact (hfac hleft).elim
    · exact hs
  · intro hs
    simp [hp.match_v2, hs]

theorem u_lt_v1_of_v2_ne_zero {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2)
    (hv1 : 0 < v1) (hv2 : v2 ≠ 0) :
    hp.u < v1 := by
  have hv2sq : 0 < v2 ^ 2 := by
    simpa using sq_pos_iff.mpr hv2
  have hu2lt : hp.u ^ 2 < v1 ^ 2 := by
    rw [hp.u_sq]
    nlinarith
  have hu_nonneg : 0 ≤ hp.u := le_of_lt hp.u_pos
  have hv1_nonneg : 0 ≤ v1 := le_of_lt hv1
  nlinarith

theorem vacuum_shift_prefactor_of_params {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) :
    2 * hp.u * hp.s ^ 2 = v1 - hp.u := by
  have hc : hp.c ^ 2 - hp.s ^ 2 = 1 := hp.hyperbolic_id
  have h1 : v1 = hp.u * (hp.c ^ 2 + hp.s ^ 2) := hp.match_v1
  calc
    2 * hp.u * hp.s ^ 2 = hp.u * (2 * hp.s ^ 2) := by ring
    _ = hp.u * (hp.c ^ 2 + hp.s ^ 2 - (hp.c ^ 2 - hp.s ^ 2)) := by ring
    _ = hp.u * (hp.c ^ 2 + hp.s ^ 2) - hp.u * (hp.c ^ 2 - hp.s ^ 2) := by ring
    _ = v1 - hp.u * 1 := by rw [← h1, hc]
    _ = v1 - hp.u := by ring

theorem concrete_velocity_match :
    concreteV1 = Bosonize.Ch17.v1Velocity concreteVF concreteG4 ∧
      concreteV2 = Bosonize.Ch17.v2Velocity concreteG2 := by
  constructor
  · rw [concreteV1, concreteVF, concreteG4, Bosonize.Ch17.v1Velocity]
    have hden : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp [hden]
    ring
  · rw [concreteV2, concreteG2, Bosonize.Ch17.v2Velocity]
    have hden : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp [hden]
    ring

theorem concreteParams_s_ne_zero :
    concreteParams.s ≠ 0 := by
  norm_num [concreteParams]

end Scalars

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

section Operators

/-- Finite dressed oscillator sum with the chapter prefactor tied to `L = 2h`.
This packages the chosen Chapter 17 pairing model only. It is intended for
identities on `A05.jointBudget h Ns K` vectors, not for a claim about a global
CCR automorphism or a finite dressed vacuum vector. -/
noncomputable def dressedOscillatorOp (h M : ℕ) (u c s : ℝ)
    (branches : Bosonize.A06.Branches σ) : Bosonize.A05.Operators σ h :=
  ((((2 * Real.pi : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ))) •
    ∑ m ∈ Finset.Icc 1 M, Bosonize.A07Interactions.dressedModeNumber h m u c s branches

theorem bogoliubov_creator_inverse_right (h m : ℕ) (hp : HyperbolicPair)
    (branches : Bosonize.A06.Branches σ) :
    Bosonize.A05.rho h branches.rightSpecies (m : ℤ) =
      (hp.c : ℂ) •
          Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches .right -
        (hp.s : ℂ) •
          Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .left := by
  have H := HyperbolicPair.inverse_combination hp
    (Bosonize.A05.rho h branches.rightSpecies (m : ℤ))
    (Bosonize.A05.rho h branches.leftSpecies (-(m : ℤ)))
  dsimp [Bosonize.A07Interactions.bogoliubovCreator, Bosonize.A07Interactions.bogoliubovAnnihilator, Bosonize.A07Interactions.oppositeOrientation, Bosonize.A06.speciesOf]
  exact H.symm

theorem bogoliubov_creator_inverse_left (h m : ℕ) (hp : HyperbolicPair)
    (branches : Bosonize.A06.Branches σ) :
    Bosonize.A05.rho h branches.leftSpecies (m : ℤ) =
      (hp.c : ℂ) •
          Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches .left -
        (hp.s : ℂ) •
          Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .right := by
  have hid := hp.hyperbolic_id
  have hidC : (hp.c : ℂ) ^ 2 - (hp.s : ℂ) ^ 2 = 1 := by
    calc
      (hp.c : ℂ) ^ 2 - (hp.s : ℂ) ^ 2 = ((hp.c ^ 2 - hp.s ^ 2 : ℝ) : ℂ) := by simp
      _ = (1 : ℝ) := by rw [hid]
      _ = 1 := by simp
  calc
    Bosonize.A05.rho h branches.leftSpecies (m : ℤ)
      = (1 : ℂ) • Bosonize.A05.rho h branches.leftSpecies (m : ℤ) := by simp
    _ = ((hp.c : ℂ) ^ 2 - (hp.s : ℂ) ^ 2) • Bosonize.A05.rho h branches.leftSpecies (m : ℤ) := by rw [hidC]
    _ = (hp.c : ℂ) ^ 2 • Bosonize.A05.rho h branches.leftSpecies (m : ℤ) - (hp.s : ℂ) ^ 2 • Bosonize.A05.rho h branches.leftSpecies (m : ℤ) := by rw [sub_smul]
    _ = (hp.c : ℂ) ^ 2 • Bosonize.A05.rho h branches.leftSpecies (m : ℤ) + ((hp.c : ℂ) * (hp.s : ℂ)) • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) -
        (((hp.c : ℂ) * (hp.s : ℂ)) • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) + (hp.s : ℂ) ^ 2 • Bosonize.A05.rho h branches.leftSpecies (m : ℤ)) := by
      abel
    _ = (hp.c : ℂ) ^ 2 • Bosonize.A05.rho h branches.leftSpecies (m : ℤ) + ((hp.c : ℂ) * (hp.s : ℂ)) • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) -
        (((hp.s : ℂ) * (hp.c : ℂ)) • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) + (hp.s : ℂ) ^ 2 • Bosonize.A05.rho h branches.leftSpecies (m : ℤ)) := by
      have hcomm : (hp.c : ℂ) * (hp.s : ℂ) = (hp.s : ℂ) * (hp.c : ℂ) := mul_comm _ _
      have : (((hp.s : ℂ) * (hp.c : ℂ)) • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) + (hp.s : ℂ) ^ 2 • Bosonize.A05.rho h branches.leftSpecies (m : ℤ)) = (((hp.c : ℂ) * (hp.s : ℂ)) • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) + (hp.s : ℂ) ^ 2 • Bosonize.A05.rho h branches.leftSpecies (m : ℤ)) := by rw [hcomm]
      rw [this]
    _ = (hp.c : ℂ) • ((hp.c : ℂ) • Bosonize.A05.rho h branches.leftSpecies (m : ℤ) + (hp.s : ℂ) • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ))) -
        (hp.s : ℂ) • ((hp.c : ℂ) • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) + (hp.s : ℂ) • Bosonize.A05.rho h branches.leftSpecies (m : ℤ)) := by
      simp [smul_add, mul_smul, pow_two]
    _ = (hp.c : ℂ) •
          Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches .left -
        (hp.s : ℂ) •
          Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .right := by
      unfold Bosonize.A07Interactions.bogoliubovCreator
      unfold Bosonize.A07Interactions.bogoliubovAnnihilator
      simp only [Bosonize.A07Interactions.oppositeOrientation, Bosonize.A06.speciesOf]

theorem bogoliubov_annihilator_inverse_right (h m : ℕ) (hp : HyperbolicPair)
    (branches : Bosonize.A06.Branches σ) :
    Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) =
      (hp.c : ℂ) •
          Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .right -
        (hp.s : ℂ) •
          Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches .left := by
  dsimp [Bosonize.A07Interactions.bogoliubovAnnihilator, Bosonize.A07Interactions.bogoliubovCreator,
         Bosonize.A06.speciesOf, Bosonize.A07Interactions.oppositeOrientation]
  have h_id : (hp.c : ℂ) ^ 2 - (hp.s : ℂ) ^ 2 = 1 := by
    have h1 : (hp.c : ℂ) ^ 2 - (hp.s : ℂ) ^ 2 = ((hp.c ^ 2 - hp.s ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, hp.hyperbolic_id, Complex.ofReal_one]
  calc
    Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ))
      = (1 : ℂ) • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) := by simp
    _ = ((hp.c : ℂ) ^ 2 - (hp.s : ℂ) ^ 2) • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) := by rw [h_id]
    _ = (hp.c : ℂ) • ((hp.c : ℂ) • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) + (hp.s : ℂ) • Bosonize.A05.rho h branches.leftSpecies (m : ℤ)) -
        (hp.s : ℂ) • ((hp.c : ℂ) • Bosonize.A05.rho h branches.leftSpecies (m : ℤ) + (hp.s : ℂ) • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ))) := by module

theorem bogoliubov_annihilator_inverse_left (h m : ℕ) (hp : HyperbolicPair)
    (branches : Bosonize.A06.Branches σ) :
    Bosonize.A05.rho h branches.leftSpecies (-(m : ℤ)) =
      (hp.c : ℂ) •
          Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .left -
        (hp.s : ℂ) •
          Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches .right := by
  exact (HyperbolicPair.inverse_combination hp
    (Bosonize.A05.rho h branches.leftSpecies (-(m : ℤ)))
    (Bosonize.A05.rho h branches.rightSpecies (m : ℤ))).symm

theorem bogoliubov_cross_annihilator_creator
    (h m : ℕ) (c s : ℝ) (branches : Bosonize.A06.Branches σ)
    (η : Bosonize.A06.Orientation) :
    Bosonize.A02.commutator
        (Bosonize.A07Interactions.bogoliubovAnnihilator h m c s branches η)
        (Bosonize.A07Interactions.bogoliubovCreator h m c s branches
          (Bosonize.A07Interactions.oppositeOrientation η)) = 0 := by
  have hdistinct : Bosonize.A06.speciesOf branches η ≠ Bosonize.A06.speciesOf branches (Bosonize.A07Interactions.oppositeOrientation η) := by
    cases η
    · exact branches.distinct
    · exact branches.distinct.symm
  have hcross (p q : ℤ) := Bosonize.A05.rho_cross_commute h (Bosonize.A06.speciesOf branches η)
    (Bosonize.A06.speciesOf branches (Bosonize.A07Interactions.oppositeOrientation η)) hdistinct p q
  have hbilin (a b : ℂ) (A B C D : Bosonize.A05.Operators σ h) :
      Bosonize.A02.commutator (a • A + b • B) (a • C + b • D) =
      (a*a) • Bosonize.A02.commutator A C + (a*b) • Bosonize.A02.commutator A D +
      (b*a) • Bosonize.A02.commutator B C + (b*b) • Bosonize.A02.commutator B D := by
    simp only [Bosonize.A02.commutator, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub]
    module
  unfold Bosonize.A07Interactions.bogoliubovAnnihilator Bosonize.A07Interactions.bogoliubovCreator
  have hop_op : Bosonize.A07Interactions.oppositeOrientation (Bosonize.A07Interactions.oppositeOrientation η) = η := by
    cases η <;> rfl
  rw [hop_op]
  rw [hbilin]
  have hreverse (A B : Bosonize.A05.Operators σ h) : Bosonize.A02.commutator B A = -Bosonize.A02.commutator A B := by
    simp only [Bosonize.A02.commutator]
    abel
  have haa := hcross (-(m : ℤ)) (m : ℤ)
  have hab : Bosonize.A02.commutator (Bosonize.A05.rho h (Bosonize.A06.speciesOf branches η) (-↑m)) (Bosonize.A05.rho h (Bosonize.A06.speciesOf branches η) (-↑m)) = 0 := by
    simp only [Bosonize.A02.commutator, sub_self]
  have hba : Bosonize.A02.commutator (Bosonize.A05.rho h (Bosonize.A06.speciesOf branches (Bosonize.A07Interactions.oppositeOrientation η)) ↑m) (Bosonize.A05.rho h (Bosonize.A06.speciesOf branches (Bosonize.A07Interactions.oppositeOrientation η)) ↑m) = 0 := by
    simp only [Bosonize.A02.commutator, sub_self]
  have hc := hcross (-(m : ℤ)) m
  rw [haa, hab, hba, hreverse, hc]
  simp

theorem bogoliubov_cross_creator_creator_on_budget
    (h M K m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (c s : ℝ)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : Bosonize.A06.branchMargins h M K Ns branches)
    (v : Bosonize.A05.FockSpace σ h) (hv : v ∈ Bosonize.A05.jointBudget h Ns K) :
    Bosonize.A02.commutator
        (Bosonize.A07Interactions.bogoliubovCreator h m c s branches .right)
        (Bosonize.A07Interactions.bogoliubovCreator h m c s branches .left) v = 0 := by
  have _ := hm
  have hcross (p q : ℤ) :
      Bosonize.A02.commutator (Bosonize.A05.rho h branches.rightSpecies p)
        (Bosonize.A05.rho h branches.leftSpecies q) = 0 :=
    Bosonize.A05.rho_cross_commute h branches.rightSpecies branches.leftSpecies
      branches.distinct p q
  have hcross' (p q : ℤ) :
      Bosonize.A02.commutator (Bosonize.A05.rho h branches.leftSpecies p)
        (Bosonize.A05.rho h branches.rightSpecies q) = 0 :=
    Bosonize.A05.rho_cross_commute h branches.leftSpecies branches.rightSpecies
      branches.distinct.symm p q
  have hbilin (a b : ℂ) (A B C D : Bosonize.A05.Operators σ h) :
      Bosonize.A02.commutator (a • A + b • B) (a • C + b • D) =
      (a * a) • Bosonize.A02.commutator A C + (a * b) • Bosonize.A02.commutator A D +
      (b * a) • Bosonize.A02.commutator B C + (b * b) • Bosonize.A02.commutator B D := by
    simp only [Bosonize.A02.commutator, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      smul_sub]
    module
  have hreverse (A B : Bosonize.A05.Operators σ h) :
      Bosonize.A02.commutator B A = -Bosonize.A02.commutator A B := by
    simp only [Bosonize.A02.commutator]
    abel
  have hmar (θ : Bosonize.A06.Orientation) :
      Bosonize.A06.marginAt h M K Ns (Bosonize.A06.speciesOf branches θ) := by
    cases θ
    · exact hmargin.1
    · exact hmargin.2
  have hCCR (θ : Bosonize.A06.Orientation) :
      Bosonize.A02.commutator
          (Bosonize.A05.rho h (Bosonize.A06.speciesOf branches θ) (-(m : ℤ)))
          (Bosonize.A05.rho h (Bosonize.A06.speciesOf branches θ) (m : ℤ)) v =
        (m : ℂ) • v := by
    have hc := Bosonize.A06.joint_signed_current_commutator h K hh Ns
      (Bosonize.A06.speciesOf branches θ) (-(m : ℤ)) (m : ℤ) (by
        have hb := hmar θ
        unfold Bosonize.A06.marginAt at hb
        simp only [abs_neg, abs_of_nonneg (Int.natCast_nonneg m)] at *
        omega) v hv
    simpa only [Bosonize.Ch10.schwingerCoefficient, neg_add_cancel, ite_true,
      Int.cast_neg, neg_neg, Int.cast_natCast] using hc
  have hCCRR :
      Bosonize.A02.commutator (Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)))
        (Bosonize.A05.rho h branches.rightSpecies (m : ℤ)) v =
        (m : ℂ) • v := by
    simpa [Bosonize.A06.speciesOf] using (hCCR .right)
  have hCCRL :
      Bosonize.A02.commutator (Bosonize.A05.rho h branches.leftSpecies (-(m : ℤ)))
        (Bosonize.A05.rho h branches.leftSpecies (m : ℤ)) v =
        (m : ℂ) • v := by
    simpa [Bosonize.A06.speciesOf] using (hCCR .left)
  unfold Bosonize.A07Interactions.bogoliubovCreator
  rw [hbilin (c : ℂ) (s : ℂ)]
  simp only [Bosonize.A07Interactions.oppositeOrientation, Bosonize.A06.speciesOf]
  have h_rev_right :=
    hreverse (Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)))
      (Bosonize.A05.rho h branches.rightSpecies (m : ℤ))
  rw [hcross (m : ℤ) (m : ℤ), h_rev_right, hcross' (-(m : ℤ)) (-(m : ℤ))]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, smul_zero,
    zero_add, add_zero]
  rw [hCCRR, hCCRL]
  module

theorem bogoliubov_cross_annihilator_annihilator_on_budget
    (h M K m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (c s : ℝ)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : Bosonize.A06.branchMargins h M K Ns branches)
    (v : Bosonize.A05.FockSpace σ h) (hv : v ∈ Bosonize.A05.jointBudget h Ns K) :
    Bosonize.A02.commutator
        (Bosonize.A07Interactions.bogoliubovAnnihilator h m c s branches .right)
        (Bosonize.A07Interactions.bogoliubovAnnihilator h m c s branches .left) v = 0 := by
  have _ := hm
  have hdistinct : Bosonize.A06.speciesOf branches .right ≠ Bosonize.A06.speciesOf branches .left :=
    branches.distinct
  have hcross (p q : ℤ) : Bosonize.A02.commutator (Bosonize.A05.rho h branches.rightSpecies p) (Bosonize.A05.rho h branches.leftSpecies q) = 0 :=
    Bosonize.A05.rho_cross_commute h (Bosonize.A06.speciesOf branches .right) (Bosonize.A06.speciesOf branches .left) hdistinct p q
  have hbilin (a b : ℂ) (A B C D : Bosonize.A05.Operators σ h) :
      Bosonize.A02.commutator (a • A + b • B) (a • C + b • D) =
      (a*a) • Bosonize.A02.commutator A C + (a*b) • Bosonize.A02.commutator A D +
      (b*a) • Bosonize.A02.commutator B C + (b*b) • Bosonize.A02.commutator B D := by
    simp only [Bosonize.A02.commutator, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub]
    module
  have hreverse (A B : Bosonize.A05.Operators σ h) : Bosonize.A02.commutator B A = -Bosonize.A02.commutator A B := by
    simp only [Bosonize.A02.commutator]
    abel
  unfold Bosonize.A07Interactions.bogoliubovAnnihilator
  rw [hbilin (c:ℂ) (s:ℂ)]
  have h_opp_R : Bosonize.A07Interactions.oppositeOrientation .right = .left := rfl
  have h_opp_L : Bosonize.A07Interactions.oppositeOrientation .left = .right := rfl
  have h_rho_L : Bosonize.A06.speciesOf branches .left = branches.leftSpecies := rfl
  have h_rho_R : Bosonize.A06.speciesOf branches .right = branches.rightSpecies := rfl
  simp only [h_opp_R, h_opp_L, h_rho_L, h_rho_R]
  rw [hcross (-↑m) (-↑m)]
  have hmar (θ : Bosonize.A06.Orientation) : Bosonize.A06.marginAt h M K Ns (Bosonize.A06.speciesOf branches θ) := by
    cases θ
    · exact hmargin.1
    · exact hmargin.2
  have hCCR (θ : Bosonize.A06.Orientation) :
      Bosonize.A02.commutator (Bosonize.A05.rho h (Bosonize.A06.speciesOf branches θ) (-(m : ℤ)))
        (Bosonize.A05.rho h (Bosonize.A06.speciesOf branches θ) (m : ℤ)) v = (m : ℂ) • v := by
    have hc := Bosonize.A06.joint_signed_current_commutator h K hh Ns (Bosonize.A06.speciesOf branches θ)
      (-(m : ℤ)) (m : ℤ) (by
        have hb := hmar θ
        unfold Bosonize.A06.marginAt at hb
        simp only [abs_neg, abs_of_nonneg (Int.natCast_nonneg m)]
        omega) v hv
    simpa only [Bosonize.Ch10.schwingerCoefficient, neg_add_cancel, ite_true,
      Int.cast_neg, neg_neg, Int.cast_natCast] using hc
  have hCCRR : (Bosonize.A02.commutator (Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)))
        (Bosonize.A05.rho h branches.rightSpecies (m : ℤ))) v = (m : ℂ) • v := hCCR .right
  have hCCRL : (Bosonize.A02.commutator (Bosonize.A05.rho h branches.leftSpecies (-(m : ℤ)))
        (Bosonize.A05.rho h branches.leftSpecies (m : ℤ))) v = (m : ℂ) • v := hCCR .left
  have h_rev_left := hreverse (Bosonize.A05.rho h branches.leftSpecies (-↑m)) (Bosonize.A05.rho h branches.leftSpecies ↑m)
  have h_rev_cross := hreverse (Bosonize.A05.rho h branches.rightSpecies ↑m) (Bosonize.A05.rho h branches.leftSpecies ↑m)
  rw [h_rev_left, h_rev_cross]
  have hcross_2 : Bosonize.A02.commutator (Bosonize.A05.rho h branches.rightSpecies ↑m) (Bosonize.A05.rho h branches.leftSpecies ↑m) = 0 := hcross ↑m ↑m
  rw [hcross_2]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    LinearMap.zero_apply, neg_zero, smul_zero, add_zero]
  rw [hCCRR, hCCRL]
  module

/-- Budgeted oscillator identity for the chosen Chapter 17 pairing model.
The intended proof sums the frozen Core per-mode theorem
`A07Interactions.bogoliubov_expansion_on_budget`; it is an action identity on
budget vectors only. -/

theorem luttinger_oscillator_dressed_on_budget
    (h M K : ℕ) (hh : 0 < h) (vF g4 g2 : ℝ) {v1 v2 : ℝ}
    (hv1 : v1 = Bosonize.Ch17.v1Velocity vF g4)
    (hv2 : v2 = Bosonize.Ch17.v2Velocity g2)
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : Bosonize.A06.branchMargins h M K Ns branches)
    (v : Bosonize.A05.FockSpace σ h) (hv : v ∈ Bosonize.A05.jointBudget h Ns K) :
    Bosonize.Ch17.luttingerOscillatorOp h M vF g4 g2 branches v =
      (dressedOscillatorOp h M hp.u hp.c hp.s branches) v -
        (((vacuumShiftScalar h M hp.u hp.s : ℝ) : ℂ)) • v := by
  unfold Bosonize.Ch17.luttingerOscillatorOp dressedOscillatorOp vacuumShiftScalar
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  have h_mode_eq : ∀ m ∈ Finset.Icc 1 M,
      Bosonize.A07Interactions.dressedModeNumber h m hp.u hp.c hp.s branches v =
      Bosonize.A07Interactions.pairingMode h m v1 v2 branches v +
      ((2 * hp.u * hp.s ^ 2 * (m : ℝ) : ℝ) : ℂ) • v := by
    intro m hm
    apply Bosonize.A07Interactions.bogoliubov_expansion_on_budget h M K m hh
      (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2 v1 v2 hp branches Ns hmargin v hv
  rw [Finset.sum_congr rfl h_mode_eq]
  rw [Finset.sum_add_distrib]
  rw [smul_add]
  subst hv1 hv2
  rw [← Finset.sum_smul]
  push_cast
  simp only [mul_smul]
  abel_nf

/-- Full finite-budget Hamiltonian identity for the chosen Chapter 17 model.
The carrier is `A05.FockSpace σ h`, the zero mode is kept as
`Ch17.zeroModeEnergyScalar`, and the statement avoids any claim that a finite
vector is a global dressed CCR vacuum. -/

theorem luttinger_hamiltonian_dressed_on_budget
    (h M K : ℕ) (hh : 0 < h) (vF g4 g2 mu : ℝ) {v1 v2 : ℝ}
    (hv1 : v1 = Bosonize.Ch17.v1Velocity vF g4)
    (hv2 : v2 = Bosonize.Ch17.v2Velocity g2)
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hSug : Bosonize.Ch17.sugawaraMargin h M K Ns branches)
    (hmargin : Bosonize.A06.branchMargins h M K Ns branches)
    (v : Bosonize.A05.FockSpace σ h) (hv : v ∈ Bosonize.A05.jointBudget h Ns K) :
    Bosonize.Ch17.luttingerFermionChosenModel h M vF g4 g2 mu branches v =
      (dressedOscillatorOp h M hp.u hp.c hp.s branches) v +
        (((Bosonize.Ch17.zeroModeEnergyScalar h vF g4 g2 mu branches Ns -
            vacuumShiftScalar h M hp.u hp.s : ℝ) : ℂ)) • v := by
  rw [Bosonize.Ch17.luttinger_hamiltonian_on_budget h M K hh vF g4 g2 mu branches Ns hN hSug v hv]
  rw [luttinger_oscillator_dressed_on_budget h M K hh vF g4 g2 hv1 hv2 hp branches Ns hmargin v hv]
  push_cast
  module

/-- Constructive right-branch witness on the finite ground ket.
The dressed lowering mode differs from the bare one by an explicit opposite
branch excitation, so this is the finite replacement for an assumed global
bare-and-dressed common vacuum. -/

theorem dressed_annihilator_ground_right
    (h m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns) :
    Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .right
        (Bosonize.A05.groundKet h Ns) =
      (hp.s : ℂ) • Bosonize.Ch16.excitedKet h Ns branches .left m := by
  have h0m : 0 < m := by
    omega
  have hground :
      Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) (Bosonize.A05.groundKet h Ns) = 0 := by
    simpa using
      Bosonize.A05.rho_lowering_budget_zero h hh branches.rightSpecies m 0 h0m Ns
        (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.ground_mem_budget h hh Ns hN 0)
  simp [Bosonize.A07Interactions.bogoliubovAnnihilator, Bosonize.Ch16.excitedKet,
    Bosonize.A06.speciesOf, Bosonize.A07Interactions.oppositeOrientation, hground]

theorem dressed_annihilator_ground_left
    (h m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns) :
    Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .left
        (Bosonize.A05.groundKet h Ns) =
      (hp.s : ℂ) • Bosonize.Ch16.excitedKet h Ns branches .right m := by
  dsimp [Bosonize.A07Interactions.bogoliubovAnnihilator, Bosonize.Ch16.excitedKet]
  have hg := Bosonize.A05.ground_mem_budget h hh Ns hN 0
  have hl (ν : σ) : Bosonize.A05.rho h ν (-(m : ℤ)) (Bosonize.A05.groundKet h Ns) = 0 :=
    Bosonize.A05.rho_lowering_budget_zero h hh ν m 0 (by omega) Ns _ hg
  simp [hl, Bosonize.A07Interactions.oppositeOrientation, Bosonize.A06.speciesOf]

theorem dressed_annihilator_ground_right_ne_zero
    (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) (hs : hp.s ≠ 0)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M m Ns (Bosonize.A06.speciesOf branches .left)) :
    Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .right
        (Bosonize.A05.groundKet h Ns) ≠ 0 := by
  intro hzero
  have hEq := dressed_annihilator_ground_right h m hh hm hp branches Ns hN
  rw [hEq] at hzero
  have hKet : Bosonize.Ch16.excitedKet h Ns branches .left m ≠ 0 :=
    Bosonize.Ch16.excited_ket_nonzero h M m hh hm hcut Ns hN branches .left hmargin
  have hs' : (hp.s : ℂ) ≠ 0 := by
    simpa using hs
  have hdisj := smul_eq_zero.mp hzero
  cases hdisj with
  | inl hs0 => exact hs' hs0
  | inr hk0 => exact hKet hk0

theorem dressed_annihilator_ground_left_ne_zero
    (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) (hs : hp.s ≠ 0)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M m Ns (Bosonize.A06.speciesOf branches .right)) :
    Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .left
        (Bosonize.A05.groundKet h Ns) ≠ 0 := by
  rw [dressed_annihilator_ground_left h m hh hm hp branches Ns hN]
  intro hz
  have hsmul : (hp.s : ℂ) • Bosonize.Ch16.excitedKet h Ns branches .right m = 0 := hz
  have hs_c_ne_zero : (hp.s : ℂ) ≠ 0 := by exact_mod_cast hs
  cases smul_eq_zero.mp hsmul with
  | inl hs_zero => exact hs_c_ne_zero hs_zero
  | inr hk_zero =>
    have hk_ne_zero := Bosonize.Ch16.excited_ket_nonzero h M m hh hm hcut Ns hN branches .right hmargin
    exact hk_ne_zero hk_zero

/-- Minimal finite-budget obstruction: a nonzero budget vector in the current
action regime cannot be annihilated simultaneously by the bare and dressed
lowering modes for one retained positive mode when `s ≠ 0`. Boundary vectors
outside the explicit budget/margin regime are intentionally excluded. -/

theorem no_common_bare_dressed_vacuum
    (h M K m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) (hs : hp.s ≠ 0)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : Bosonize.A06.branchMargins h M K Ns branches)
    (ψ : Bosonize.A05.FockSpace σ h) (hψ : ψ ≠ 0)
    (hψbudget : ψ ∈ Bosonize.A05.jointBudget h Ns K)
    (hbareR : Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) ψ = 0)
    (hbareL : Bosonize.A05.rho h branches.leftSpecies (-(m : ℤ)) ψ = 0)
    (hdressR :
      Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .right ψ = 0)
    (hdressL :
      Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .left ψ = 0) :
    False := by
  have _ := hdressL
  have H := hdressR
  change ((hp.c : ℂ) • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) +
          (hp.s : ℂ) • Bosonize.A05.rho h branches.leftSpecies (m : ℤ)) ψ = 0 at H
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply] at H
  rw [hbareR, smul_zero, zero_add] at H
  have hs_c : (hp.s : ℂ) ≠ 0 := by
    intro h_eq
    apply hs
    exact_mod_cast h_eq
  have H2 : (Bosonize.A05.rho h branches.leftSpecies (m : ℤ)) ψ = 0 := by
    exact smul_eq_zero.mp H |>.resolve_left hs_c
  have H3 : Bosonize.A02.commutator (Bosonize.A05.rho h branches.leftSpecies (m : ℤ)) (Bosonize.A05.rho h branches.leftSpecies (-(m : ℤ))) ψ = 0 := by
    change (Bosonize.A05.rho h branches.leftSpecies (m : ℤ)) ((Bosonize.A05.rho h branches.leftSpecies (-(m : ℤ))) ψ) -
           (Bosonize.A05.rho h branches.leftSpecies (-(m : ℤ))) ((Bosonize.A05.rho h branches.leftSpecies (m : ℤ)) ψ) = 0
    rw [H2, hbareL, map_zero, map_zero, sub_zero]
  have Hmargin_L : |(m : ℤ)| + |-(m : ℤ)| + (K : ℤ) + |Ns branches.leftSpecies| ≤ (h : ℤ) := by
    dsimp [Bosonize.A06.branchMargins] at hmargin
    have HmL : |(m : ℤ)| ≤ (M : ℤ) := by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast hcut
    have Hm2L : |-(m : ℤ)| ≤ (M : ℤ) := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      exact_mod_cast hcut
    have HmL_add : |(m : ℤ)| + |-(m : ℤ)| ≤ 2 * (M : ℤ) := by omega
    have HmL_M : 2 * (M : ℤ) + (K : ℤ) + |Ns branches.leftSpecies| ≤ (h : ℤ) := hmargin.2
    omega
  have H4 := Bosonize.A06.joint_signed_current_commutator h K hh Ns branches.leftSpecies (m : ℤ) (-(m : ℤ)) Hmargin_L ψ hψbudget
  rw [H3] at H4
  have H5 : Bosonize.Ch10.schwingerCoefficient (m : ℤ) (-(m : ℤ)) = -(m : ℂ) := by
    unfold Bosonize.Ch10.schwingerCoefficient
    have h_add : (m : ℤ) + -(m : ℤ) = 0 := by abel
    simp [h_add]
  rw [H5] at H4
  have H6 : (-(m : ℂ)) • ψ = 0 := H4.symm
  have H7 : (-(m : ℂ)) ≠ 0 := by
    intro H_eq
    have H_eq_0 : (m : ℂ) = 0 := by exact neg_eq_zero.mp H_eq
    have H_eq_0' : (m : ℤ) = 0 := by exact_mod_cast H_eq_0
    have H_gt_0 : (m : ℤ) > 0 := by exact_mod_cast hm
    omega
  exact hψ (smul_eq_zero.mp H6 |>.resolve_left H7)

theorem concrete_bogoliubov_witness :
    Bosonize.A05.admissible concreteCarrierH concreteNs ∧
      Bosonize.A06.branchMargins concreteCarrierH concreteCutoff concreteBudget
        concreteNs concreteBranches ∧
      Bosonize.Ch17.sugawaraMargin concreteCarrierH concreteCutoff concreteBudget
        concreteNs concreteBranches ∧
      concreteParams.s ≠ 0 ∧
      Bosonize.A05.groundKet concreteCarrierH concreteNs ∈
        Bosonize.A05.jointBudget concreteCarrierH concreteNs concreteBudget ∧
      Bosonize.A05.groundKet concreteCarrierH concreteNs ≠ 0 ∧
      Bosonize.A07Interactions.bogoliubovAnnihilator concreteCarrierH concreteMode
          concreteParams.c concreteParams.s concreteBranches .right
          (Bosonize.A05.groundKet concreteCarrierH concreteNs) ≠ 0 ∧
      Bosonize.A07Interactions.dressedModeNumber concreteCarrierH concreteMode
          concreteParams.u concreteParams.c concreteParams.s concreteBranches
          (Bosonize.A05.groundKet concreteCarrierH concreteNs) ≠ 0 ∧
      vacuumShiftScalar concreteCarrierH concreteCutoff concreteParams.u concreteParams.s ≠ 0 ∧
      vacuumShiftScalar concreteCarrierH concreteCutoff concreteParams.u concreteParams.s =
        27 * Real.pi / 8 ∧
      luttingerG concretePair = 1 / 4 ∧
      2 * concreteParams.u * concreteParams.s ^ 2 = 9 := by
  have concrete_bogoliubov_witness_part1 : Bosonize.A05.admissible concreteCarrierH concreteNs := by
    intro ν
    dsimp [Bosonize.A05.admissible, concreteNs, Bosonize.Ch07.admissible]
    constructor <;> norm_num
  have concrete_bogoliubov_witness_part2 : Bosonize.A06.branchMargins concreteCarrierH concreteCutoff concreteBudget concreteNs concreteBranches := by
    constructor <;> norm_num [Bosonize.A06.branchMargins, Bosonize.A06.marginAt, concreteCarrierH, concreteCutoff, concreteBudget, concreteNs]
  have concrete_bogoliubov_witness_part3 : Bosonize.Ch17.sugawaraMargin concreteCarrierH concreteCutoff concreteBudget concreteNs concreteBranches := by
    simp [Bosonize.Ch17.sugawaraMargin, concreteCarrierH, concreteCutoff, concreteBudget, concreteNs]
  have concrete_bogoliubov_witness_part4 : concreteParams.s ≠ 0 := by
    norm_num [concreteParams]
  have concrete_bogoliubov_witness_part5 : Bosonize.A05.groundKet concreteCarrierH concreteNs ∈ Bosonize.A05.jointBudget concreteCarrierH concreteNs concreteBudget := by
    simpa [concreteCarrierH, concreteNs, concreteBudget] using
      (Bosonize.A05.ground_mem_budget concreteCarrierH (by norm_num [concreteCarrierH])
        concreteNs (by
          intro ν
          constructor <;> norm_num [concreteNs]) concreteBudget)
  have concrete_bogoliubov_witness_part6 : Bosonize.A05.groundKet concreteCarrierH concreteNs ≠ 0 := by
    show Bosonize.A02.ket (Bosonize.A05.groundConfiguration concreteCarrierH concreteNs) ≠ 0
    exact Bosonize.A02.ket_ne_zero (Bosonize.A05.groundConfiguration concreteCarrierH concreteNs)
  have concrete_bogoliubov_witness_part7 : Bosonize.A07Interactions.bogoliubovAnnihilator concreteCarrierH concreteMode concreteParams.c concreteParams.s concreteBranches .right (Bosonize.A05.groundKet concreteCarrierH concreteNs) ≠ 0 := by
    apply dressed_annihilator_ground_right_ne_zero concreteCarrierH concreteCutoff concreteMode
      (by decide) (by decide) (by decide) concreteParams concreteParams_s_ne_zero concreteBranches concreteNs concrete_bogoliubov_witness_part1
    rcases concrete_bogoliubov_witness_part2 with ⟨_, h⟩
    exact h
  have concrete_bogoliubov_witness_part8 : Bosonize.A07Interactions.dressedModeNumber concreteCarrierH concreteMode concreteParams.u concreteParams.c concreteParams.s concreteBranches (Bosonize.A05.groundKet concreteCarrierH concreteNs) ≠ 0 := by
    let g := Bosonize.A05.groundKet concreteCarrierH concreteNs
    let D := Bosonize.A07Interactions.dressedModeNumber concreteCarrierH concreteMode
      concreteParams.u concreteParams.c concreteParams.s concreteBranches
    let CR := Bosonize.A07Interactions.bogoliubovCreator concreteCarrierH concreteMode
      concreteParams.c concreteParams.s concreteBranches .right
    let AR := Bosonize.A07Interactions.bogoliubovAnnihilator concreteCarrierH concreteMode
      concreteParams.c concreteParams.s concreteBranches .right
    let CL := Bosonize.A07Interactions.bogoliubovCreator concreteCarrierH concreteMode
      concreteParams.c concreteParams.s concreteBranches .left
    let AL := Bosonize.A07Interactions.bogoliubovAnnihilator concreteCarrierH concreteMode
      concreteParams.c concreteParams.s concreteBranches .left
    intro hz
    have hz_inner : inner ℂ g (D g) = 0 := by rw [hz, inner_zero_right]
    change inner ℂ g ((concreteParams.u : ℂ) • (CR (AR g) + CL (AL g))) = 0 at hz_inner
    rw [inner_smul_right, inner_add_right] at hz_inner
    have hadjR := Bosonize.A07Interactions.bogoliubov_creator_adjoint
      concreteCarrierH concreteMode concreteParams.c concreteParams.s concreteBranches .right
    have hinnerR := LinearMap.adjoint_inner_left CR (AR g) g
    rw [hadjR] at hinnerR
    have hadjL := Bosonize.A07Interactions.bogoliubov_creator_adjoint
      concreteCarrierH concreteMode concreteParams.c concreteParams.s concreteBranches .left
    have hinnerL := LinearMap.adjoint_inner_left CL (AL g) g
    rw [hadjL] at hinnerL
    rw [← hinnerR, ← hinnerL] at hz_inner
    have hu : (concreteParams.u : ℂ) ≠ 0 := by norm_num [concreteParams]
    have hsum : inner ℂ (AR g) (AR g) + inner ℂ (AL g) (AL g) = 0 :=
      (mul_eq_zero.mp hz_inner).resolve_left hu
    have hre : RCLike.re (inner ℂ (AR g) (AR g)) + RCLike.re (inner ℂ (AL g) (AL g)) = 0 := by
      have h_re_sum := congrArg RCLike.re hsum
      rw [map_add, map_zero] at h_re_sum
      exact h_re_sum
    have hL_nonneg : 0 ≤ RCLike.re (inner ℂ (AL g) (AL g)) := inner_self_nonneg
    have hAR_ne : AR g ≠ 0 := by
      have hh : 0 < concreteCarrierH := by decide
      have hm : 1 ≤ concreteMode := by decide
      have hcut : concreteMode ≤ concreteCutoff := by decide
      have hs : concreteParams.s ≠ 0 := concreteParams_s_ne_zero
      have hN : Bosonize.A05.admissible concreteCarrierH concreteNs := by
        intro ν; simp only [concreteNs, Bosonize.Ch07.admissible]; omega
      have hmargin : Bosonize.A06.marginAt concreteCarrierH concreteCutoff concreteMode
          concreteNs (Bosonize.A06.speciesOf concreteBranches .left) := by
        simp [Bosonize.A06.marginAt, concreteNs, concreteCarrierH, concreteCutoff, concreteMode]
      exact dressed_annihilator_ground_right_ne_zero concreteCarrierH concreteCutoff concreteMode
        hh hm hcut concreteParams hs concreteBranches concreteNs hN hmargin
    have hR_pos : 0 < RCLike.re (inner ℂ (AR g) (AR g)) := by
      have hnonneg : 0 ≤ RCLike.re (inner ℂ (AR g) (AR g)) := inner_self_nonneg
      have hnz : inner ℂ (AR g) (AR g) ≠ 0 := inner_self_ne_zero.mpr hAR_ne
      have heq : ((RCLike.re (inner ℂ (AR g) (AR g)) : ℝ) : ℂ) = inner ℂ (AR g) (AR g) :=
        inner_self_ofReal_re (𝕜 := ℂ) (AR g)
      apply lt_of_le_of_ne hnonneg
      intro he
      apply hnz
      rw [← heq, ← he, Complex.ofReal_zero]
    have h_pos : 0 < RCLike.re (inner ℂ (AR g) (AR g)) + RCLike.re (inner ℂ (AL g) (AL g)) :=
      add_pos_of_pos_of_nonneg hR_pos hL_nonneg
    linarith
  have concrete_bogoliubov_witness_part9 : vacuumShiftScalar concreteCarrierH concreteCutoff concreteParams.u concreteParams.s ≠ 0 := by
    unfold vacuumShiftScalar concreteCarrierH concreteCutoff concreteParams
    have h : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by
      ext x
      simp
      omega
    rw [h]
    have h1 : (1 : ℕ) ∉ ({2} : Finset ℕ) := by simp
    rw [Finset.sum_insert h1, Finset.sum_singleton]
    apply ne_of_gt
    apply mul_pos
    · apply div_pos
      · exact mul_pos (by norm_num) Real.pi_pos
      · norm_num
    · norm_num
  have concrete_bogoliubov_witness_part10 : vacuumShiftScalar concreteCarrierH concreteCutoff concreteParams.u concreteParams.s = 27 * Real.pi / 8 := by
    unfold vacuumShiftScalar
    have hCut : Finset.Icc 1 concreteCutoff = {1, 2} := by
      dsimp [concreteCutoff]
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hCut, Finset.sum_insert (by decide), Finset.sum_singleton]
    dsimp [concreteCarrierH, concreteParams]
    norm_num
    ring
  have concrete_bogoliubov_witness_part11 : luttingerG concretePair = 1 / 4 := by
    dsimp [luttingerG, concretePair, HyperbolicPair.ofParams, concreteParams]
    norm_num
  have concrete_bogoliubov_witness_part12 : 2 * concreteParams.u * concreteParams.s ^ 2 = 9 := by
    norm_num [concreteParams]
  exact ⟨concrete_bogoliubov_witness_part1, concrete_bogoliubov_witness_part2, concrete_bogoliubov_witness_part3, concrete_bogoliubov_witness_part4, concrete_bogoliubov_witness_part5, concrete_bogoliubov_witness_part6, concrete_bogoliubov_witness_part7, concrete_bogoliubov_witness_part8, concrete_bogoliubov_witness_part9, concrete_bogoliubov_witness_part10, concrete_bogoliubov_witness_part11, concrete_bogoliubov_witness_part12⟩

end Operators

end Bosonize.Ch18
