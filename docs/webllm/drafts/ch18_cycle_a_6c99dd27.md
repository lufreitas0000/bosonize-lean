## Source map

- Reviewed guidance: `docs/webllm/guidance/ch18_phase_a_sources.md`. This draft treats every source claim as a proposal for review, not as verified truth.
- Frozen Core reused without redefinition:
  - `Bosonize.Core.A07InteractionsAndBogoliubov`: `HyperbolicParams`, `pairingMode`, `bogoliubovCreator`, `bogoliubovAnnihilator`, `dressedModeNumber`, `bogoliubov_expansion_on_budget`, `bogoliubov_ccr_on_budget`, `pairing_mode_ground_nonzero`, `raw_inter_eq_hopping`.
  - `Bosonize.Core.A05MultiSpecies` and `Bosonize.Core.A06ChiralFields`: actual finite carrier `A05.FockSpace σ h`, operator carrier `A05.Operators σ h`, branch data `A06.Branches`, and budget/margin predicates.
  - `Bosonize.Core.Ch16FieldHamiltonian`: `excitedKet`, `excited_ket_nonzero`, and the standard two-branch witness carrier.
  - `Bosonize.Core.Ch17LuttingerModels`: the Chapter 17 chosen pairing model, `v1Velocity`, `v2Velocity`, `luttingerOscillatorOp`, `luttingerFermionChosenModel`, `zeroModeEnergyScalar`, `sugawaraMargin`.
  - `Bosonize.Core.A10DiscreteSchriefferWolff`: cited in prose for energy-shell vs. mode-decimation review obligations; not re-proved here.
- Literature anchors in the guidance ledger are used only to motivate statement shapes and convention choices. The formal draft below relies on the Core API rather than on fresh CCR hypotheses.
- Main source discrepancy kept explicit: the raw finite inter-branch density-density term factors into the hopping model, while Chapter 17 deliberately chooses the pairing model. The draft therefore diagonalizes only the chosen Chapter 17 pairing Hamiltonian on budget vectors.

## Design and scope

- Carrier and operators:
  - finite Hilbert carrier: `A05.FockSpace σ h`;
  - endomorphism carrier: `A05.Operators σ h = Module.End ℂ (A05.FockSpace σ h)`.
- Signs and branches:
  - the plus-sign transform follows the frozen Core convention
    `C̃_R = c ρ_{m,R} + s ρ_{-m,L}` and `C̃_L = c ρ_{m,L} + s ρ_{-m,R}`;
  - inverse formulas are proposed as global linear algebra consequences of `c^2 - s^2 = 1`.
- Budgets and hypotheses:
  - operator identities are stated on `A05.jointBudget h Ns K` vectors only;
  - same-branch dressed CCR and the diagonalization sum depend on `A06.branchMargins h M K Ns branches` and on the existing Core budget theorems;
  - the full Chapter 17 Hamiltonian statement keeps `A05.admissible`, `Ch17.sugawaraMargin`, and `A06.branchMargins` separate rather than conflating them.
- Prefactors and length:
  - every oscillator prefactor is tied to `L = 2h` through `((2 * Real.pi : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ)`;
  - the proposed vacuum shift is a finite scalar normal-ordering correction with the same `2h` convention.
- Finite-budget caveats carried into docstrings and prose:
  - chosen pairing model only;
  - identity on budget vectors, not a global algebra automorphism;
  - no claim that a finite vector is a dressed vacuum for an infinite CCR representation.
- Explicit nonzero witness required by scope:
  - scalar witness `(v1,v2,u,c,s) = (17,15,8,5/4,3/4)`;
  - carrier witness `h = 8`, `M = 2`, `K = 2`, `Ns = 0`, `branches = Ch16.standardBranches`;
  - `s ≠ 0`, nonzero dressed lowering action on the finite ground ket, and `vacuumShiftScalar = 27 π / 8` are stated as review targets.
- Namespace/module plan:
  - `BosonizeStubs/Ch18Bogoliubov.lean` reopens `Bosonize.Ch18` once, with the scalar wrappers and explicit witness first and the budgeted operator identities and constructive vacuum-obstruction statements afterward.

## Lean draft

```lean
import Bosonize.Core.A07InteractionsAndBogoliubov
import Bosonize.Core.Ch16FieldHamiltonian
import Bosonize.Core.Ch17LuttingerModels

-- BEGIN_MODULE BosonizeStubs/Ch18Bogoliubov.lean
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
    (hp.c - hp.s) * (hp.c + hp.s) = 1 := by sorry

lemma HyperbolicPair.c_sub_s_ne_zero (hp : HyperbolicPair) :
    hp.c - hp.s ≠ 0 := by sorry

lemma HyperbolicPair.c_add_s_ne_zero (hp : HyperbolicPair) :
    hp.c + hp.s ≠ 0 := by sorry

/-- Carrier-independent Lemma 18.3 for reuse on other carriers. -/
theorem HyperbolicPair.inverse_combination {E : Type*} [AddCommGroup E] [Module ℂ E]
    (hp : HyperbolicPair) (X Y : E) :
    (hp.c : ℂ) • ((hp.c : ℂ) • X + (hp.s : ℂ) • Y) -
      (hp.s : ℂ) • ((hp.c : ℂ) • Y + (hp.s : ℂ) • X) = X := by sorry

theorem hyperbolic_params_nonempty (v1 v2 : ℝ) (hstab : |v2| < v1) :
    Nonempty (Bosonize.A07Interactions.HyperbolicParams v1 v2) := by sorry

theorem tanh_relation_of_params {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) :
    v2 * (hp.c ^ 2 + hp.s ^ 2) = v1 * (2 * hp.c * hp.s) := by sorry

theorem luttingerG_mul_inv (hp : HyperbolicPair) :
    luttingerG hp * luttingerGInv hp = 1 := by sorry

theorem luttingerGInv_eq_inv (hp : HyperbolicPair) :
    luttingerGInv hp = (luttingerG hp)⁻¹ := by sorry

theorem luttingerG_mul_u_of_params {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) :
    luttingerG (HyperbolicPair.ofParams hp) * hp.u = v1 - v2 := by sorry

theorem luttingerGInv_mul_u_of_params {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) :
    luttingerGInv (HyperbolicPair.ofParams hp) * hp.u = v1 + v2 := by sorry

theorem luttingerG_eq_sqrt_of_params {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) :
    luttingerG (HyperbolicPair.ofParams hp) = Real.sqrt ((v1 - v2) / (v1 + v2)) := by sorry

theorem luttingerG_pos_of_params {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) :
    0 < luttingerG (HyperbolicPair.ofParams hp) := by sorry
theorem luttingerGInv_pos_of_params {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) :
    0 < luttingerGInv (HyperbolicPair.ofParams hp) := by sorry

theorem hyperbolic_coeff_eq_luttinger (hp : HyperbolicPair) :
    hp.c ^ 2 + hp.s ^ 2 = (luttingerG hp + (luttingerG hp)⁻¹) / 2 := by sorry

theorem v2_eq_zero_iff_s_eq_zero {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) :
    v2 = 0 ↔ hp.s = 0 := by sorry

theorem u_lt_v1_of_v2_ne_zero {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2)
    (hv1 : 0 < v1) (hv2 : v2 ≠ 0) :
    hp.u < v1 := by sorry

theorem vacuum_shift_prefactor_of_params {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) :
    2 * hp.u * hp.s ^ 2 = v1 - hp.u := by sorry

theorem concrete_velocity_match :
    concreteV1 = Bosonize.Ch17.v1Velocity concreteVF concreteG4 ∧
      concreteV2 = Bosonize.Ch17.v2Velocity concreteG2 := by sorry

theorem concreteParams_s_ne_zero :
    concreteParams.s ≠ 0 := by sorry

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
          Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .left := by sorry

theorem bogoliubov_creator_inverse_left (h m : ℕ) (hp : HyperbolicPair)
    (branches : Bosonize.A06.Branches σ) :
    Bosonize.A05.rho h branches.leftSpecies (m : ℤ) =
      (hp.c : ℂ) •
          Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches .left -
        (hp.s : ℂ) •
          Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .right := by sorry

theorem bogoliubov_annihilator_inverse_right (h m : ℕ) (hp : HyperbolicPair)
    (branches : Bosonize.A06.Branches σ) :
    Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) =
      (hp.c : ℂ) •
          Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .right -
        (hp.s : ℂ) •
          Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches .left := by sorry

theorem bogoliubov_annihilator_inverse_left (h m : ℕ) (hp : HyperbolicPair)
    (branches : Bosonize.A06.Branches σ) :
    Bosonize.A05.rho h branches.leftSpecies (-(m : ℤ)) =
      (hp.c : ℂ) •
          Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .left -
        (hp.s : ℂ) •
          Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches .right := by sorry

theorem bogoliubov_cross_annihilator_creator
    (h m : ℕ) (c s : ℝ) (branches : Bosonize.A06.Branches σ)
    (η : Bosonize.A06.Orientation) :
    Bosonize.A02.commutator
        (Bosonize.A07Interactions.bogoliubovAnnihilator h m c s branches η)
        (Bosonize.A07Interactions.bogoliubovCreator h m c s branches
          (Bosonize.A07Interactions.oppositeOrientation η)) = 0 := by sorry

theorem bogoliubov_cross_creator_creator_on_budget
    (h M K m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (c s : ℝ)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : Bosonize.A06.branchMargins h M K Ns branches)
    (v : Bosonize.A05.FockSpace σ h) (hv : v ∈ Bosonize.A05.jointBudget h Ns K) :
    Bosonize.A02.commutator
        (Bosonize.A07Interactions.bogoliubovCreator h m c s branches .right)
        (Bosonize.A07Interactions.bogoliubovCreator h m c s branches .left) v = 0 := by sorry

theorem bogoliubov_cross_annihilator_annihilator_on_budget
    (h M K m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (c s : ℝ)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : Bosonize.A06.branchMargins h M K Ns branches)
    (v : Bosonize.A05.FockSpace σ h) (hv : v ∈ Bosonize.A05.jointBudget h Ns K) :
    Bosonize.A02.commutator
        (Bosonize.A07Interactions.bogoliubovAnnihilator h m c s branches .right)
        (Bosonize.A07Interactions.bogoliubovAnnihilator h m c s branches .left) v = 0 := by sorry

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
        (((vacuumShiftScalar h M hp.u hp.s : ℝ) : ℂ)) • v := by sorry

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
            vacuumShiftScalar h M hp.u hp.s : ℝ) : ℂ)) • v := by sorry

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
      (hp.s : ℂ) • Bosonize.Ch16.excitedKet h Ns branches .left m := by sorry

theorem dressed_annihilator_ground_left
    (h m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns) :
    Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .left
        (Bosonize.A05.groundKet h Ns) =
      (hp.s : ℂ) • Bosonize.Ch16.excitedKet h Ns branches .right m := by sorry

theorem dressed_annihilator_ground_right_ne_zero
    (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) (hs : hp.s ≠ 0)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M m Ns (Bosonize.A06.speciesOf branches .left)) :
    Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .right
        (Bosonize.A05.groundKet h Ns) ≠ 0 := by sorry

theorem dressed_annihilator_ground_left_ne_zero
    (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) (hs : hp.s ≠ 0)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M m Ns (Bosonize.A06.speciesOf branches .right)) :
    Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .left
        (Bosonize.A05.groundKet h Ns) ≠ 0 := by sorry

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
    False := by sorry

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
      2 * concreteParams.u * concreteParams.s ^ 2 = 9 := by sorry

end Operators

end Bosonize.Ch18
-- END_MODULE BosonizeStubs/Ch18Bogoliubov.lean
```

## Companion notebook

- Scalar review notebook tasks:
  - check that `luttingerG`, `luttingerGInv`, `g u = v1 - v2`, `g⁻¹ u = v1 + v2`, and `2us^2 = v1 - u` use only `HyperbolicParams` fields and never a hidden sign choice;
  - verify that `v2 = 0 ↔ s = 0` and `u < v1` really require the stated positivity hypotheses.
- Operator review notebook tasks:
  - expand the inverse transform with exact branch labels and signs;
  - derive the finite-sum dressed oscillator identity from the frozen per-mode theorem `A07Interactions.bogoliubov_expansion_on_budget` rather than from ad hoc commutation hypotheses;
  - combine that sum with `Ch17.luttinger_hamiltonian_on_budget` for the full Chapter 17 statement.
- Witness notebook tasks:
  - evaluate the explicit witness `(17,15,8,5/4,3/4)`;
  - confirm `Ch17.v1Velocity 1 (32π) = 17` and `Ch17.v2Velocity (30π) = 15`;
  - check `vacuumShiftScalar 8 2 8 (3/4) = 27π/8` and hence nonzero;
  - inspect that the dressed lowering action on the finite ground ket is nonzero because it lands on an explicit `Ch16.excitedKet` witness, not because a global dressed vacuum is assumed.
- SW review notebook tasks:
  - cite Core results `A10.energy_shell_discards_double_mode_one` and `A10.sw_off_zero_implies_effective_exact` when discussing shell projection;
  - keep the shell-vs-mode-decimation distinction conceptual and separate from the Bogoliubov diagonalization proof obligations above.

## Review obligations

- Human mathematical review is required before any integration or freezing.
- Reviewers should confirm all of the following without weakening statements:
  - the transform is the plus-sign, opposite-branch pairing convention already frozen in Core;
  - every prefactor is tied to `L = 2h`;
  - the draft diagonalizes only the chosen Chapter 17 pairing model, not the raw finite `g2` density-density term;
  - every operator theorem is budgeted on the actual finite carrier `A05.FockSpace σ h` and does not smuggle in global CCR assumptions;
  - admissibility, `sugawaraMargin`, and `branchMargins` remain explicit and are not merged into a vacuous wrapper;
  - the obstruction theorem is read as a current-action statement on nonzero budget vectors, not as a global claim on every finite basis ket;
  - the explicit witness with `s ≠ 0` is checked concretely: `(v1,v2,u,c,s) = (17,15,8,5/4,3/4)` and `(h,M,K,Ns) = (8,2,2,0)`;
  - no later chapter should infer a dressed finite vacuum or a unitary implementer from these budgeted identities alone.
- Only after that review should the proposed module path `BosonizeStubs/Ch18Bogoliubov.lean` be considered for staging.