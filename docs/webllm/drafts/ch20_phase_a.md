## Source map

This is an **unverified Phase A proposal**, not a proof or a modification of frozen Core. Packet `ch20_phase_a-20261016T133230Z-dbc49307`, baseline `d555477a75e28da8e75d5e6e88518fdce173c9aa`. The source paths and hashes below are from the packet manifest (SHA-256). The manifest also records the editable target's pre-response hash (the empty-file hash); that is packet-baseline metadata, not a source. The source guidance itself is unverified; its literature anchors are not independent validations of the proposed Lean contracts.

| Source path | SHA-256 |
|---|---|
| `packets/ch20_phase_a.toml` | `33a1f7255f0b31fc98a3989e686c0cdab531354206b3dfcbe43ffd77608616c7` |
| `docs/webllm/guidance/ch20_phase_a_sources.md` | `f52d501a08c032d96ee9d9384b77604b2d8e00da6cd8143e074aecf60db6045f` |
| `notes/md/ch20_CDW.md` | `29a1016437b6fbc310c455fec6d15c1216e16b048eb12c34885b647deca87f78` |
| `notes/appendices/a08_states_and_correlations.md` | `3d6f94da8336bc46503c3b8b7a91db852dd2429ce558259eaefcd0a8f280d9b5` |
| `notes/appendices/a09_duality_spin_and_umklapp.md` | `f2d22dd41ea1381c3c63c31917c8806d768761d55e4529daf1e0039e47c894a9` |
| `Bosonize/Core/Ch14Mandelstam.lean` | `0d3feed562023e5d8a20027021014cc56512d636b58848fa7a8122b61cc320fc` |
| `Bosonize/Core/Ch16FieldHamiltonian.lean` | `54e045da25fcc31e8e18bce5b81b1318adef6955e38ca357e3b7b6c21887e787` |
| `Bosonize/Core/Ch17LuttingerModels.lean` | `9355fcc40f2ec1e5d9ac5ef07065ee8d03a957d8329ef9d5d528e7f1f2e3223c` |
| `Bosonize/Core/Ch18Bogoliubov.lean` | `b55da072fac73055173cd65e584751caabdd02f2473648725b09e11c6fbc314b` |
| `Bosonize/Core/A05MultiSpecies.lean` | `bb9055adcf9358d5f2274666205d31dc3073716fe53e5f6bf02a983f92335bc2` |
| `Bosonize/Core/A06ChiralFields.lean` | `77c579ff06238d2801e9861fdf65c5c1efc66fc31d0161efd18a6a386d2fa768` |
| `Bosonize/Core/A07InteractionsAndBogoliubov.lean` | `1e96db0038b2ae7f012e16d1f6d5a98b43b33661d31f4220cdf3399530fca59f` |
| `scripts/webllm/verify_phase_a.py` | `b70ef27ece09ef4222fc6f6e4cdc4b7809697697765167a2c6e3856a6bcefbbf` |
| `lean-toolchain` | `8f89aa44fccdb1a0b6cc768c7c9f54b94cd40e47a08d582f82d1235f13075cf7` |
| `lakefile.toml` | `ff92810c2e3c8013e04745790ac4b1a96d84135917973a667c11dbbe75bf0cb0` |
| `docs/spec/core_locks.json` | `bc9ce182054f83c82062bbc8d21878e79b4f6d234842443d002b06a7c4dab1ac` |

Primary contracts are `docs/webllm/guidance/ch20_phase_a_sources.md` §D, `notes/md/ch20_CDW.md` §§20.1–20.3, and `notes/appendices/a09_duality_spin_and_umklapp.md` for the duality convention. `notes/appendices/a08_states_and_correlations.md` is contextual/deferred, not an imported interface. The finite operators and projection API are from `Bosonize/Core/A05MultiSpecies.lean` and `Bosonize/Core/Ch14Mandelstam.lean`; the two-branch and interacting-mode APIs are from `Bosonize/Core/A06ChiralFields.lean`, `Bosonize/Core/Ch16FieldHamiltonian.lean`, `Bosonize/Core/Ch17LuttingerModels.lean`, `Bosonize/Core/A07InteractionsAndBogoliubov.lean`, and `Bosonize/Core/Ch18Bogoliubov.lean`.

## Design and scope

The single proposed module is `Bosonize/Core/Ch20CDW.lean` (staging candidate may be kept separately), namespace `Bosonize.Ch20`. Only four **Core** modules are directly imported; transitive prerequisites provide A01/A02/A03/A05/A06/A07/Ch13. Each claimed operator acts on the actual finite multispecies CAR Fock space. A source label `Ns`, an intermediate label `lowerCharge Ns L`, and a target label are distinct, and `Ch14.projectedMap` fixes *both* the charge sector and the excitation cutoff. `Ch14.budgetAdjoint` is only applied after explicitly reversing its carrier arguments.

The scalar coefficient laws use the canonical root `A01.canonicalRoot (2*h)` and periodic twists; a general boundary twist would contribute `Ch06Ext.liftPhase`. The fermionic factor order is always `c_R† * c_L` for CDW and `c_R * c_L` for SC, with the left annihilator acting first. For the finite witnesses the fixed order is `Fin 2`, right species `0` and left species `1`. `K` denotes only a cutoff, never the Luttinger parameter, called `luttingerG` here.

Duality in this Phase A candidate is **only** a sign substitution on *mode families*, reflection of charge labels, and scalar coefficient identities. It is not a linear/star/unitary map on the finite CAR Fock Hilbert space or the absent A08 oscillator/charge tensor algebra. Consequently, no finite-Fock unitary equivalence, spectral invariance, analytic limit, power law, Gaussian state, or full Weyl vertex assertion follows. No projection remainder may be discarded without a subsequently proved range/final-projection cancellation. The symmetric zero-mode equality is deliberately separate from the unadjusted linear-chemical-potential counterexample.

## Lean draft

```lean
import Bosonize.Core.Ch14Mandelstam
import Bosonize.Core.Ch16FieldHamiltonian
import Bosonize.Core.Ch17LuttingerModels
import Bosonize.Core.Ch18Bogoliubov

namespace Bosonize.Ch20

open scoped BigOperators Classical

section FiniteCAR

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

/-- Raise one source charge, without changing any other species. -/
noncomputable def raiseCharge (Ns : σ → ℤ) (ν : σ) : σ → ℤ :=
  Function.update Ns ν (Ns ν + 1)

/-- Reflect only the left charge label; this is not a Fock-space operator. -/
noncomputable def reflectLeft (branches : A06.Branches σ) (Ns : σ → ℤ) : σ → ℤ :=
  Function.update Ns branches.leftSpecies (-(Ns branches.leftSpecies))

noncomputable def cdwTarget (branches : A06.Branches σ) (Ns : σ → ℤ) : σ → ℤ :=
  raiseCharge (Ch13.lowerCharge Ns branches.leftSpecies) branches.rightSpecies

noncomputable def scTarget (branches : A06.Branches σ) (Ns : σ → ℤ) : σ → ℤ :=
  Ch13.lowerCharge (Ch13.lowerCharge Ns branches.leftSpecies) branches.rightSpecies

noncomputable def cdwShift (branches : A06.Branches σ) (ν : σ) : ℤ :=
  (if ν = branches.rightSpecies then (1 : ℤ) else 0) -
    (if ν = branches.leftSpecies then (1 : ℤ) else 0)

noncomputable def scShift (branches : A06.Branches σ) (ν : σ) : ℤ :=
  -(if ν = branches.rightSpecies then (1 : ℤ) else 0) -
    (if ν = branches.leftSpecies then (1 : ℤ) else 0)

lemma lowerCharge_raiseCharge (Ns : σ → ℤ) (ν : σ) :
    Ch13.lowerCharge (raiseCharge Ns ν) ν = Ns := by sorry

lemma raiseCharge_lowerCharge (Ns : σ → ℤ) (ν : σ) :
    raiseCharge (Ch13.lowerCharge Ns ν) ν = Ns := by sorry

lemma cdwTarget_apply (branches : A06.Branches σ) (Ns : σ → ℤ) (ν : σ) :
    cdwTarget branches Ns ν = Ns ν + cdwShift branches ν := by sorry

lemma scTarget_apply (branches : A06.Branches σ) (Ns : σ → ℤ) (ν : σ) :
    scTarget branches Ns ν = Ns ν + scShift branches ν := by sorry

lemma reflectLeft_involutive (branches : A06.Branches σ) (Ns : σ → ℤ) :
    reflectLeft branches (reflectLeft branches Ns) = Ns := by sorry

lemma cdwTarget_lower_right (branches : A06.Branches σ) (Ns : σ → ℤ) :
    Ch13.lowerCharge (cdwTarget branches Ns) branches.rightSpecies =
      Ch13.lowerCharge Ns branches.leftSpecies := by sorry

/-- The actual A05 position annihilator; creation is its true adjoint. -/
noncomputable def fieldOf (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (ν : σ) (x : ℤ) : A05.Operators σ h :=
  A05.liftedAnnihilation h b ν x

noncomputable def orderCDW (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) : A05.Operators σ h :=
  LinearMap.adjoint (fieldOf h b branches.rightSpecies x) *
    fieldOf h b branches.leftSpecies x

noncomputable def orderSC (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) : A05.Operators σ h :=
  fieldOf h b branches.rightSpecies x * fieldOf h b branches.leftSpecies x

/-- The discarded intermediate channel is a genuine ambient CAR operator. -/
noncomputable def cdwResidualOp (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ) (Km : ℕ) :
    A05.Operators σ h :=
  LinearMap.adjoint (fieldOf h b branches.rightSpecies x) *
    (1 - Ch14.projection h (Ch13.lowerCharge Ns branches.leftSpecies) Km) *
    fieldOf h b branches.leftSpecies x

noncomputable def scResidualOp (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ) (Km : ℕ) :
    A05.Operators σ h :=
  fieldOf h b branches.rightSpecies x *
    (1 - Ch14.projection h (Ch13.lowerCharge Ns branches.leftSpecies) Km) *
    fieldOf h b branches.leftSpecies x

/-- Global CAR charge law; no budget or spurious cutoff assumption. -/
lemma orderCDW_charge_commutator (h : ℕ)
    (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (ν : σ) :
    A02.commutator (A05.chargeObservable h ν) (orderCDW h b branches x) =
      ((cdwShift branches ν : ℤ) : ℂ) • orderCDW h b branches x := by sorry

lemma orderSC_charge_commutator (h : ℕ)
    (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (ν : σ) :
    A02.commutator (A05.chargeObservable h ν) (orderSC h b branches x) =
      ((scShift branches ν : ℤ) : ℂ) • orderSC h b branches x := by sorry

/-- Insert `Pm + (1 - Pm)` *between* the two actual field factors. -/
lemma ambient_cdw_residual (h : ℕ)
    (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ)
    (Ks Km Kt : ℕ) :
    Ch14.projection h (cdwTarget branches Ns) Kt * orderCDW h b branches x *
        Ch14.projection h Ns Ks =
      Ch14.projection h (cdwTarget branches Ns) Kt *
        LinearMap.adjoint (fieldOf h b branches.rightSpecies x) *
        Ch14.projection h (Ch13.lowerCharge Ns branches.leftSpecies) Km *
        fieldOf h b branches.leftSpecies x * Ch14.projection h Ns Ks +
      Ch14.projection h (cdwTarget branches Ns) Kt *
        cdwResidualOp h b branches x Ns Km * Ch14.projection h Ns Ks := by sorry

lemma ambient_sc_residual (h : ℕ)
    (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ)
    (Ks Km Kt : ℕ) :
    Ch14.projection h (scTarget branches Ns) Kt * orderSC h b branches x *
        Ch14.projection h Ns Ks =
      Ch14.projection h (scTarget branches Ns) Kt *
        fieldOf h b branches.rightSpecies x *
        Ch14.projection h (Ch13.lowerCharge Ns branches.leftSpecies) Km *
        fieldOf h b branches.leftSpecies x * Ch14.projection h Ns Ks +
      Ch14.projection h (scTarget branches Ns) Kt *
        scResidualOp h b branches x Ns Km * Ch14.projection h Ns Ks := by sorry

/-- Source → intermediate → CDW target, plus a typed retained residual. -/
lemma projected_cdw_residual (h : ℕ)
    (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ)
    (Ks Km Kt : ℕ) :
    Ch14.projectedMap h Ns (cdwTarget branches Ns) Ks Kt (orderCDW h b branches x) =
      (Ch14.projectedMap h (Ch13.lowerCharge Ns branches.leftSpecies)
          (cdwTarget branches Ns) Km Kt
          (LinearMap.adjoint (fieldOf h b branches.rightSpecies x))).comp
        (Ch14.projectedMap h Ns (Ch13.lowerCharge Ns branches.leftSpecies) Ks Km
          (fieldOf h b branches.leftSpecies x)) +
      Ch14.projectedMap h Ns (cdwTarget branches Ns) Ks Kt
        (cdwResidualOp h b branches x Ns Km) := by sorry

lemma projected_sc_residual (h : ℕ)
    (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ)
    (Ks Km Kt : ℕ) :
    Ch14.projectedMap h Ns (scTarget branches Ns) Ks Kt (orderSC h b branches x) =
      (Ch14.projectedMap h (Ch13.lowerCharge Ns branches.leftSpecies)
          (scTarget branches Ns) Km Kt
          (fieldOf h b branches.rightSpecies x)).comp
        (Ch14.projectedMap h Ns (Ch13.lowerCharge Ns branches.leftSpecies) Ks Km
          (fieldOf h b branches.leftSpecies x)) +
      Ch14.projectedMap h Ns (scTarget branches Ns) Ks Kt
        (scResidualOp h b branches x Ns Km) := by sorry

/-- The CDW creation factor is the reversed-carrier adjoint, not a label. -/
lemma cdw_creation_factor_eq_budgetAdjoint (h : ℕ)
    (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ)
    (Km Kt : ℕ) :
    Ch14.projectedMap h (Ch13.lowerCharge Ns branches.leftSpecies)
        (cdwTarget branches Ns) Km Kt
        (LinearMap.adjoint (fieldOf h b branches.rightSpecies x)) =
      Ch14.budgetAdjoint h (cdwTarget branches Ns)
        (Ch13.lowerCharge Ns branches.leftSpecies) Kt Km
        (Ch14.projectedMap h (cdwTarget branches Ns)
          (Ch13.lowerCharge Ns branches.leftSpecies) Kt Km
          (fieldOf h b branches.rightSpecies x)) := by sorry

/-- Source-charge phase and the *ordered* Klein factors, in the periodic gauge. -/
noncomputable def cdwChargeCoeff (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (x : ℤ) : ℂ :=
  A01.integerCharacter (A01.canonicalRoot (2 * h))
      (Ns branches.leftSpecies - Ns branches.rightSpecies - 1) x *
    (Ch13.kleinPhase h Ns branches.leftSpecies *
      Ch13.kleinPhase h (cdwTarget branches Ns) branches.rightSpecies)

noncomputable def scChargeCoeff (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (x : ℤ) : ℂ :=
  A01.integerCharacter (A01.canonicalRoot (2 * h))
      (Ns branches.rightSpecies + Ns branches.leftSpecies) x *
    (Ch13.kleinPhase h Ns branches.leftSpecies *
      Ch13.kleinPhase h (Ch13.lowerCharge Ns branches.leftSpecies)
        branches.rightSpecies)

/-- Matrix coefficient of actual CAR fields; not a bosonized-vertex identity. -/
lemma orderCDW_ground_coeff (h : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hR : Ns branches.rightSpecies < (h : ℤ))
    (hL : -(h : ℤ) < Ns branches.leftSpecies) (x : ℤ) :
    inner ℂ (A05.groundKet h (cdwTarget branches Ns))
      (orderCDW h (fun _ => Ch06Ext.periodicTwist (2 * h)) branches x
        (A05.groundKet h Ns)) =
      (((2 * h : ℕ) : ℂ)⁻¹) * cdwChargeCoeff h branches Ns x := by sorry

lemma orderSC_ground_coeff (h : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hR : -(h : ℤ) < Ns branches.rightSpecies)
    (hL : -(h : ℤ) < Ns branches.leftSpecies) (x : ℤ) :
    inner ℂ (A05.groundKet h (scTarget branches Ns))
      (orderSC h (fun _ => Ch06Ext.periodicTwist (2 * h)) branches x
        (A05.groundKet h Ns)) =
      (((2 * h : ℕ) : ℂ)⁻¹) * scChargeCoeff h branches Ns x := by sorry

/-- Scalar Klein laws for reflection. They hold for either species order. -/
lemma klein_reflect_right (h : ℕ) (branches : A06.Branches σ) (Ns : σ → ℤ) :
    Ch13.kleinPhase h (reflectLeft branches Ns) branches.rightSpecies =
      Ch13.kleinPhase h Ns branches.rightSpecies := by sorry

lemma klein_reflect_left (h : ℕ) (branches : A06.Branches σ) (Ns : σ → ℤ) :
    Ch13.kleinPhase h (reflectLeft branches Ns) branches.leftSpecies =
      -Ch13.kleinPhase h (raiseCharge Ns branches.leftSpecies)
        branches.leftSpecies := by sorry

lemma cdw_target_dual (branches : A06.Branches σ) (Ns : σ → ℤ) :
    reflectLeft branches (cdwTarget branches (reflectLeft branches Ns)) =
      raiseCharge (raiseCharge Ns branches.rightSpecies) branches.leftSpecies := by sorry

lemma scTarget_reverse_double_raise (branches : A06.Branches σ) (Ns : σ → ℤ) :
    scTarget branches (raiseCharge (raiseCharge Ns branches.rightSpecies)
      branches.leftSpecies) = Ns := by sorry

lemma sc_target_dual (branches : A06.Branches σ) (Ns : σ → ℤ) :
    reflectLeft branches (scTarget branches (reflectLeft branches Ns)) =
      raiseCharge (Ch13.lowerCharge Ns branches.rightSpecies)
        branches.leftSpecies := by sorry

lemma cdwTarget_reverse_shift (branches : A06.Branches σ) (Ns : σ → ℤ) :
    cdwTarget branches
      (raiseCharge (Ch13.lowerCharge Ns branches.rightSpecies)
        branches.leftSpecies) = Ns := by sorry

/-- Scalar shadow of the adjoint duality, including the indispensable χ(1,x). -/
lemma cdw_charge_duality (h : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ) (x : ℤ) :
    cdwChargeCoeff h branches (reflectLeft branches Ns) x =
      A01.integerCharacter (A01.canonicalRoot (2 * h)) 1 x *
        star (scChargeCoeff h branches
          (raiseCharge (raiseCharge Ns branches.rightSpecies)
            branches.leftSpecies) x) := by sorry

lemma sc_charge_duality (h : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ) (x : ℤ) :
    scChargeCoeff h branches (reflectLeft branches Ns) x =
      A01.integerCharacter (A01.canonicalRoot (2 * h)) 1 x *
        star (cdwChargeCoeff h branches
          (raiseCharge (Ch13.lowerCharge Ns branches.rightSpecies)
            branches.leftSpecies) x) := by sorry

lemma cdwChargeCoeff_norm (h : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ) (x : ℤ) :
    ‖cdwChargeCoeff h branches Ns x‖ = 1 := by sorry

lemma scChargeCoeff_norm (h : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ) (x : ℤ) :
    ‖scChargeCoeff h branches Ns x‖ = 1 := by sorry

end FiniteCAR

section FiniteWitnesses

/-- Actual two-species source charge sector (0,0). -/
def witnessZero : Fin 2 → ℤ := fun _ => 0

/-- Actual two-species source charge sector (1,0). -/
def witnessSC : Fin 2 → ℤ := ![1, 0]

lemma witnessZero_admissible : A05.admissible 2 witnessZero := by sorry

lemma concrete_cdw_coefficient :
    cdwChargeCoeff 2 Ch16.standardBranches witnessZero 1 = Complex.I := by sorry

lemma concrete_sc_coefficient :
    scChargeCoeff 2 Ch16.standardBranches witnessSC 1 = Complex.I := by sorry

lemma concrete_order_witness_cdw :
    inner ℂ (A05.groundKet 2 (cdwTarget Ch16.standardBranches witnessZero))
      (orderCDW 2 (fun _ => Ch06Ext.periodicTwist 4)
        Ch16.standardBranches 1 (A05.groundKet 2 witnessZero)) =
      Complex.I / 4 := by sorry

lemma concrete_order_witness_sc :
    inner ℂ (A05.groundKet 2 (scTarget Ch16.standardBranches witnessSC))
      (orderSC 2 (fun _ => Ch06Ext.periodicTwist 4)
        Ch16.standardBranches 1 (A05.groundKet 2 witnessSC)) =
      Complex.I / 4 := by sorry

/-- Nonzero discarded L-hole, after the R creation and target projection. -/
lemma concrete_discarded_channel_nonzero :
    Ch14.projectedMap 2 witnessZero (cdwTarget Ch16.standardBranches witnessZero)
        0 1 (cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
          Ch16.standardBranches 1 witnessZero 0)
        (Ch14.groundVector 2 (by decide) witnessZero witnessZero_admissible 0) ≠ 0 := by sorry

/-- A *different* target cutoff removes the same discarded channel. -/
lemma concrete_discarded_channel_target_zero :
    Ch14.projectedMap 2 witnessZero (cdwTarget Ch16.standardBranches witnessZero)
        0 0 (cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
          Ch16.standardBranches 1 witnessZero 0)
        (Ch14.groundVector 2 (by decide) witnessZero witnessZero_admissible 0) = 0 := by sorry

lemma concrete_orderSC_nonzero :
    orderSC 2 (fun _ => Ch06Ext.periodicTwist 4) Ch16.standardBranches 1 ≠ 0 := by sorry

end FiniteWitnesses

section ModeFamilyDuality

/-- This parameter operation changes v₂ to -v₂, not the CAR representation. -/
def dualPair (hp : Ch18.HyperbolicPair) : Ch18.HyperbolicPair where
  c := hp.c
  s := -hp.s
  hyperbolic_id := by simpa only [neg_sq] using hp.hyperbolic_id

/-- Full hyperbolic witness with sign-reversed interaction; no data `sorry`. -/
def dualParams {v1 v2 : ℝ}
    (lp : A07Interactions.HyperbolicParams v1 v2) :
    A07Interactions.HyperbolicParams v1 (-v2) where
  u := lp.u
  c := lp.c
  s := -lp.s
  u_pos := lp.u_pos
  c_pos := lp.c_pos
  u_sq := by simpa only [neg_sq] using lp.u_sq
  hyperbolic_id := by simpa only [neg_sq] using lp.hyperbolic_id
  match_v1 := by simpa only [neg_sq] using lp.match_v1
  match_v2 := by
    simpa only [mul_neg] using congrArg Neg.neg lp.match_v2

/-- An indexed pair of ambient endomorphism families, not an oscillator quotient. -/
abbrev ModeFamily (E : Type*) [AddCommGroup E] [Module ℂ E] :=
  A06.Orientation → ℤ → Module.End ℂ E

noncomputable def speciesFamily {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h : ℕ) (branches : A06.Branches σ) : ModeFamily (A05.FockSpace σ h) :=
  fun η k => A05.rho h (A06.speciesOf branches η) k

/-- D on mode families: right changes sign; left is unchanged. -/
def dualFamily {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) : ModeFamily E :=
  fun η k => match η with
    | .right => -ρ .right k
    | .left => ρ .left k

noncomputable def dressedCreatorOf {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (c s : ℝ) (η : A06.Orientation) (m : ℕ) :
    Module.End ℂ E :=
  (c : ℂ) • ρ η (m : ℤ) +
    (s : ℂ) • ρ (A07Interactions.oppositeOrientation η) (-(m : ℤ))

noncomputable def dressedAnnihilatorOf {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (c s : ℝ) (η : A06.Orientation) (m : ℕ) :
    Module.End ℂ E :=
  (c : ℂ) • ρ η (-(m : ℤ)) +
    (s : ℂ) • ρ (A07Interactions.oppositeOrientation η) (m : ℤ)

/-- Term-for-term A07 pairing expression, with its original word order. -/
noncomputable def pairingModeOf {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (m : ℕ) (v1 v2 : ℝ) : Module.End ℂ E :=
  (v1 : ℂ) •
      (ρ .right (m : ℤ) * ρ .right (-(m : ℤ)) +
       ρ .left (m : ℤ) * ρ .left (-(m : ℤ))) +
    (v2 : ℂ) •
      (ρ .right (m : ℤ) * ρ .left (m : ℤ) +
       ρ .right (-(m : ℤ)) * ρ .left (-(m : ℤ)))

/-- Finite dressed phase of an arbitrary mode family; no self-adjoint claim. -/
noncomputable def chiralPhaseOf {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (h M : ℕ) (c s : ℝ)
    (η : A06.Orientation) (x : ℤ) : Module.End ℂ E :=
  ∑ m ∈ Finset.Icc 1 M,
    ((m : ℂ)⁻¹) •
      (A01.integerCharacter (A01.canonicalRoot (2 * h))
          (-(A06.orientationSign η) * (m : ℤ)) x •
          dressedCreatorOf ρ c s η m +
       A01.integerCharacter (A01.canonicalRoot (2 * h))
          (A06.orientationSign η * (m : ℤ)) x •
          dressedAnnihilatorOf ρ c s η m)

noncomputable def xCDWOf {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (h M : ℕ) (hp : Ch18.HyperbolicPair)
    (x : ℤ) : Module.End ℂ E :=
  ((hp.c - hp.s : ℝ) : ℂ) •
    (chiralPhaseOf ρ h M hp.c hp.s .right x +
      chiralPhaseOf ρ h M hp.c hp.s .left x)

noncomputable def xSCOf {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (h M : ℕ) (hp : Ch18.HyperbolicPair)
    (x : ℤ) : Module.End ℂ E :=
  ((hp.c + hp.s : ℝ) : ℂ) •
    (chiralPhaseOf ρ h M hp.c hp.s .right x -
      chiralPhaseOf ρ h M hp.c hp.s .left x)

/-- D₁, a finite real-valued trigonometric kernel, not a correlator. -/
noncomputable def logKernel (h M : ℕ) (x y : ℤ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M,
    (1 - Real.cos
      ((2 * Real.pi * (m : ℝ) * ((x - y : ℤ) : ℝ)) /
        ((2 * h : ℕ) : ℝ))) / (m : ℝ)

lemma dualPair_involutive (hp : Ch18.HyperbolicPair) :
    dualPair (dualPair hp) = hp := by sorry

/-- Indexed parameter records have different syntactic fibers; state involution
on the physical coordinates rather than an ill-typed heterogeneous equality. -/
lemma dualParams_involutive {v1 v2 : ℝ}
    (lp : A07Interactions.HyperbolicParams v1 v2) :
    (dualParams (dualParams lp)).u = lp.u ∧
    (dualParams (dualParams lp)).c = lp.c ∧
    (dualParams (dualParams lp)).s = lp.s := by sorry

lemma luttingerG_dual (hp : Ch18.HyperbolicPair) :
    Ch18.luttingerG (dualPair hp) = Ch18.luttingerGInv hp := by sorry

lemma luttingerGInv_dual (hp : Ch18.HyperbolicPair) :
    Ch18.luttingerGInv (dualPair hp) = Ch18.luttingerG hp := by sorry

lemma dualParams_pair {v1 v2 : ℝ}
    (lp : A07Interactions.HyperbolicParams v1 v2) :
    Ch18.HyperbolicPair.ofParams (dualParams lp) =
      dualPair (Ch18.HyperbolicPair.ofParams lp) := by sorry

lemma v2Velocity_neg (g2 : ℝ) :
    Ch17.v2Velocity (-g2) = -Ch17.v2Velocity g2 := by sorry

/-- Exact bridge to the *current* ambient finite CAR density modes. -/
lemma dressedCreatorOf_species {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h m : ℕ) (c s : ℝ) (branches : A06.Branches σ)
    (η : A06.Orientation) :
    dressedCreatorOf (speciesFamily h branches) c s η m =
      A07Interactions.bogoliubovCreator h m c s branches η := by sorry

lemma dressedAnnihilatorOf_species {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h m : ℕ) (c s : ℝ) (branches : A06.Branches σ)
    (η : A06.Orientation) :
    dressedAnnihilatorOf (speciesFamily h branches) c s η m =
      A07Interactions.bogoliubovAnnihilator h m c s branches η := by sorry

lemma pairingModeOf_species {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h m : ℕ) (v1 v2 : ℝ) (branches : A06.Branches σ) :
    pairingModeOf (speciesFamily h branches) m v1 v2 =
      A07Interactions.pairingMode h m v1 v2 branches := by sorry

lemma dualFamily_involutive {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) :
    dualFamily (dualFamily ρ) = ρ := by sorry

/-- Cross commutators acquire a minus sign, even for arbitrary families. -/
lemma dual_commutator {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (η η' : A06.Orientation) (m n : ℤ) :
    A02.commutator (dualFamily ρ η m) (dualFamily ρ η' n) =
      (if η = η' then (1 : ℂ) else -1) •
        A02.commutator (ρ η m) (ρ η' n) := by sorry

lemma dual_dressed_creator_right {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (c s : ℝ) (m : ℕ) :
    dressedCreatorOf (dualFamily ρ) c s .right m =
      -dressedCreatorOf ρ c (-s) .right m := by sorry

lemma dual_dressed_creator_left {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (c s : ℝ) (m : ℕ) :
    dressedCreatorOf (dualFamily ρ) c s .left m =
      dressedCreatorOf ρ c (-s) .left m := by sorry

lemma dual_dressed_annihilator_right {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (c s : ℝ) (m : ℕ) :
    dressedAnnihilatorOf (dualFamily ρ) c s .right m =
      -dressedAnnihilatorOf ρ c (-s) .right m := by sorry

lemma dual_dressed_annihilator_left {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (c s : ℝ) (m : ℕ) :
    dressedAnnihilatorOf (dualFamily ρ) c s .left m =
      dressedAnnihilatorOf ρ c (-s) .left m := by sorry

lemma dual_chiralPhase_right {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (h M : ℕ) (c s : ℝ) (x : ℤ) :
    chiralPhaseOf (dualFamily ρ) h M c s .right x =
      -chiralPhaseOf ρ h M c (-s) .right x := by sorry

lemma dual_chiralPhase_left {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (h M : ℕ) (c s : ℝ) (x : ℤ) :
    chiralPhaseOf (dualFamily ρ) h M c s .left x =
      chiralPhaseOf ρ h M c (-s) .left x := by sorry

/-- The negative signs are fixed by φ = R+L and θ = R-L. -/
lemma dual_xCDW {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (h M : ℕ) (hp : Ch18.HyperbolicPair) (x : ℤ) :
    xCDWOf (dualFamily ρ) h M hp x =
      -xSCOf ρ h M (dualPair hp) x := by sorry

lemma dual_xSC {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (h M : ℕ) (hp : Ch18.HyperbolicPair) (x : ℤ) :
    xSCOf (dualFamily ρ) h M hp x =
      -xCDWOf ρ h M (dualPair hp) x := by sorry

/-- Pairing-family substitution; *not* a finite-Fock spectral equivalence. -/
lemma dual_pairingMode {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (m : ℕ) (v1 v2 : ℝ) :
    pairingModeOf (dualFamily ρ) m v1 v2 =
      pairingModeOf ρ m v1 (-v2) := by sorry

/-- The chemical-potential-adjusted symmetric charge scalar transforms exactly. -/
lemma dual_symmetric_zero_mode {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h : ℕ) (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) :
    Ch17.symmetricZeroModeScalar h vF g4 g2 branches (reflectLeft branches Ns) =
      Ch17.symmetricZeroModeScalar h vF g4 (-g2) branches Ns := by sorry

lemma dual_canonical_mu_zero_mode {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h : ℕ) (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) :
    Ch17.zeroModeEnergyScalar h vF g4 g2 (Ch17.canonicalMu h vF)
        branches (reflectLeft branches Ns) =
      Ch17.zeroModeEnergyScalar h vF g4 (-g2) (Ch17.canonicalMu h vF)
        branches Ns := by sorry

lemma logKernel_self (h M : ℕ) (x : ℤ) :
    logKernel h M x x = 0 := by sorry

lemma logKernel_symm (h M : ℕ) (x y : ℤ) :
    logKernel h M x y = logKernel h M y x := by sorry

lemma logKernel_nonneg (h M : ℕ) (x y : ℤ) :
    0 ≤ logKernel h M x y := by sorry

end ModeFamilyDuality

section DualityWitnesses

lemma concrete_luttingerG :
    Ch18.luttingerG Ch18.concretePair = (1 / 4 : ℝ) := by sorry

lemma concrete_luttingerG_dual :
    Ch18.luttingerG (dualPair Ch18.concretePair) = (4 : ℝ) := by sorry

lemma concrete_dualPair_ne :
    dualPair Ch18.concretePair ≠ Ch18.concretePair := by sorry

/-- A nontrivial v₂ = 15 pairing term changes on the actual finite Fock ket. -/
lemma concrete_pairing_duality_nontrivial :
    pairingModeOf (speciesFamily 8 Ch16.standardBranches) 1 17 15
        (A05.groundKet 8 Ch18.concreteNs) ≠
      pairingModeOf (speciesFamily 8 Ch16.standardBranches) 1 17 (-15)
        (A05.groundKet 8 Ch18.concreteNs) := by sorry

lemma concrete_logKernel : logKernel 2 1 1 0 = 1 := by sorry

/-- The *unadjusted* linear-μ term breaks the purported dual zero-mode law. -/
lemma concrete_linear_mu_counterexample :
    Ch17.zeroModeEnergyScalar 1 1 0 0 1 Ch16.standardBranches
        (![0, 1] : Fin 2 → ℤ) ≠
      Ch17.zeroModeEnergyScalar 1 1 0 0 1 Ch16.standardBranches
        (![0, -1] : Fin 2 → ℤ) := by sorry

end DualityWitnesses

end Bosonize.Ch20
```

## Companion notebook

**Carrier and import ledger.** The code uses `A05.FockSpace σ h` and `A05.Operators σ h` for the uncompressed finite occupation CAR algebra; `A05.jointBudget h Ns K` for each of the three individually typed charge/cutoff spaces; `Module.End ℂ E` for generic algebraic mode families; `σ → ℤ` for charge labels; `ℂ` for Klein/character coefficients; and `ℝ` for the finite logarithmic kernel and hyperbolic parameters. The only direct imports are `Bosonize.Core.Ch14Mandelstam`, `Bosonize.Core.Ch16FieldHamiltonian`, `Bosonize.Core.Ch17LuttingerModels`, and `Bosonize.Core.Ch18Bogoliubov`. No Mathlib umbrella import, staging import, CH19/A08 carrier, locally installed notation, invented Fock star-equivalence, or arbitrary source-independent field map occurs.

**Exact signature and source-to-contract index.** The theorem headers in the single Lean fence are normative proposed signatures (no implicit intended additional parameters). The groups below mirror them and their source anchors:

| Proposed declarations | Origin and dependency | Carrier/hypothesis rationale |
|---|---|---|
| `raiseCharge`, `reflectLeft`, `cdwTarget`, `scTarget`, `cdwShift`, `scShift`; their inverse, application, and involution lemmas | Guidance §D0; `Ch13.lowerCharge`; `A06.Branches.distinct` | Charge labels `σ → ℤ`; no state/representation |
| `fieldOf`, `orderCDW`, `orderSC`, their charge commutators | Guidance §D1, claims c01–c02; A05 finite CAR; N20 (20.1–20.2) | Actual species R≠L, global CAR endomorphisms, `LinearMap.adjoint` of the right field |
| `cdwResidualOp`, `scResidualOp`, `ambient_*_residual` | Guidance §D1 c03; A03 projector-product remainder; N20 (20.3–20.4) | Keep explicit `1-Pm` intermediate excitation leakage at *any* cutoffs |
| `projected_*_residual`; `cdw_creation_factor_eq_budgetAdjoint` | Ch14 `projectedMap`, `projected_map_adjoint`; N20 Lemma 20.2 | Source `(Ns,Ks)` → middle `(Ns-eL,Km)` → target `(Nt,Kt)`; reversed carriers for CDW † |
| `cdwChargeCoeff`, `scChargeCoeff`, `order*_ground_coeff` | Guidance §D2 c05, Ch13 `kleinPhase`, A01 `integerCharacter`, Ch14 `zeroScalar`; N20 after (20.4) | Periodic twist, canonical root, position integer, source Klein phase acts first; boundary conditions on occupied/empty edge modes |
| `concrete_*` in `FiniteWitnesses` | Guidance §D1 c06–c07; N20 after (20.4) | h=2, L=4, R=0, L=1; explicit nonzero coefficient, operator, and residual at Kt=1; contrast Kt=0 |
| `klein_reflect_*`, `*_target_dual`, `*_reverse_*`, `*_charge_duality`, `*_norm` | Guidance §D2 c13–c14, A09 §§charge/Klein; A01 root/conjugation facts | Scalar, label-level adjoint shadow only, with `χ(1,x)` correction; no A08 `D` claimed |
| `dualPair`, `dualParams`, `dualPair_involutive`, `dualParams_involutive`, `luttingerG*_dual`, `dualParams_pair`, `v2Velocity_neg` | Guidance §D3 c10; A07 `HyperbolicParams`; Ch18 `HyperbolicPair`, `luttingerG`, `luttingerGInv`; Ch17 `v2Velocity` | Constructed record with c fixed/s negated, u and v1 fixed, v2 sign reversed; g and gInv exchange |
| `ModeFamily`, `speciesFamily`, `dualFamily`, `dressed*Of`, `pairingModeOf`, bridges to A07, dual family/dressed/commutator/pairing laws | Guidance §D3 c11–c12,c15; A05 `rho`; A07 density pairing/Bogoliubov definitions | Endomorphisms indexed by orientation/mode; `dual_commutator` gives the cross sign, not an unsupported ambient star automorphism |
| `chiralPhaseOf`, `xCDWOf`, `xSCOf`, `dual_chiralPhase_*`, `dual_x*` | Guidance §D3; Ch15 conventions cited in guidance; N20 (20.6–20.7),(20.10) | Finite sums of mode-family endomorphisms, not formal vertices or expectation values |
| `dual_symmetric_zero_mode`, `dual_canonical_mu_zero_mode`, `concrete_linear_mu_counterexample` | Guidance §D3 c15–c16; Ch17 `symmetricZeroModeScalar`, `zero_mode_scalar_canonical_mu` | Symmetry of adjusted quadratic charge scalar only; explicit failure for unadjusted μ |
| `logKernel`, `logKernel_self`, `logKernel_symm`, `logKernel_nonneg`, `concrete_logKernel` | Guidance c08/D3; N20 (20.5) | Truncated real cosine sum; no limit, correlator, or `t = 1` construction |
| `concrete_*` in `DualityWitnesses` | Guidance §D3 c18; Ch18 `concretePair`, `concreteNs`; A07 `pairing_mode_ground_nonzero`; A05 `rho_lowering_budget_zero` | g=1/4→4, nonfixed s, actual nonzero v2 pairing on h=8 sea; no spectral equivalence |

**Dependency and proof order.** First check definitional equalities for updates, `Ch13.lowerCharge`, and the exact R/L order. Next elaborate the finite fields and projection formulas using `A03.projection_product_remainder` and `Ch14.projected_map_apply`; establish the reversed-carrier adjoint using `Ch14.projected_map_adjoint`. Independently derive charge commutators from A05 CAR and the diagonal charge observable. Then prove the two ground matrix coefficients by `Ch14.physical_ground_expansion`/A05 occupation signs, with periodic twist normalization and strict band-edge margins. The explicit `h=2` witnesses are independent checks of signs and projection leakage, *not* substitutes for general proofs. Prove label/Klein scalar duality separately; construct and check the hyperbolic data before working on family/phase and pairing equations. Finally establish kernel elementary properties and the μ counterexample.

**Margin and non-vacuity obligations.** `0 < h` makes `2*h` positive and the canonical root primitive in the scalar theorems. `A05.admissible h Ns` ensures a valid source sea; `Ns R < h` permits the right creation and `-h < Ns L` permits the left annihilation for CDW; for SC both lowering operations require `-h < Ns R`, `-h < Ns L`. There are deliberately no extra budget-margin assumptions on the *residual identities*: those are exact equalities even when budgets truncate the intermediate state. The finite ground-to-ground coefficients `i/4`, SC operator nonzero, and `Kt=1` discarded-channel output are explicit F2 guards. `Kt=0` provides the contrasting cancellation. The dual pairing witness has `h=8`, `m=1`, `v2=15≠0` and admits an A06 positive-mode margin, whereas the parameter witness has `s=3/4≠0`; the kernel example has `h=2,M=1` and nonzero separation. The μ counterexample has different numeric scalar energies `π−1` and `1`.

**Proposals accepted/adapted/rejected.** Accepted: source-carrier CAR order words, canonical Fourier phase, explicit three projected carriers, source-to-middle-to-target residual, scalar Klein convention, constructed parameter sign flip, finite family transformation, and symmetric quadratic zero mode. Adapted: the guidance's `HyperbolicPair.dual` is named `dualPair` in this module so that no foreign Core namespace is extended; there is no unverified `LuttingerParams` field `g`, since `g` is computed from `Ch18.luttingerG`. Concrete witness admissibility is a **named theorem obligation**, not hidden proof data. Rejected: `import Mathlib`, A08/staging imports, field-independent placeholder maps, same-species pairing, any `True` target, a direct CDW→SC exchange without adjoint/root phase, and a finite-Fock star/unitary implementation of `D`.

**Deferred CH20b and CH21 ledger.** CH20b, conditional on a reviewed CH19/A08 uncompressed state carrier, owns formal `W_J` vertices in a defined noncommutative series carrier, Hermitian phase proof, Gaussian/Wick moments, `[X_J(x),X_J(y)]`, coefficientwise correlators and variances (20.8–20.9), tensor-algebra automorphism `D`, the complete adjoint/`ζ^x` identity (20.10), and state pullback/transport (20.11b). Theorem 14.5 single-factor CAR-to-vertex equalities remain independent prerequisites; an analytic `t=1` evaluation, continuum power law, finite-CAR correlator equality, and finite-Fock spectral/T-duality are not inferred. CH21 owns spin/charge separation, parity sublattices, Umklapp charge shifts, and effective Hamiltonians.

## Review obligations

1. **Core API audit:** verify the four imports expose `A02.commutator`, `A01.integerCharacter`/`canonicalRoot`, `Ch13.lowerCharge`/`kleinPhase`, the exact `Ch14.projectedMap`/`budgetAdjoint` signatures, A05 `Operators`/`jointBudget`/`liftedAnnihilation`, A07 pairing modes, Ch17 scalars, and promoted Ch18 hyperbolic declarations. In particular verify `LinearMap.adjoint` resolves against the frozen A05 Hilbert-space instances and its lexicographic `speciesOrder`/LT/LE/DecidableEq choices; the current guidance does not guarantee instance synthesis in a new module.
2. **Charge and product checks:** confirm `A02.commutator = A*B-B*A`, both orientations are distinct, `Ch13.lowerCharge` updates the specified component, all target label identities use `FunLike`/function extensionality with no hidden 2-species assumption, and source→intermediate→target compositions have exactly the claimed `A05.jointBudget` domains. Check ring multiplication associativity and `A03.projection_product_remainder` against the literal ambient equation.
3. **Adjoint and occupation signs:** check the CAR creation is the adjoint of the *full* twisted field, not a speciesless `siteCreation`; compare ground actions with the A05 `Ch04.fermionSign` preceding-count ordering. Validate the exponent `Ns L - Ns R - 1` (CDW), `Ns R + Ns L` (SC), the use of `Ch13.kleinPhase h (cdwTarget Ns) R` vs. `Ch13.kleinPhase h (lower Ns L) R`, and the explicit `Complex.I/4` witnesses. Confirm the strict endpoint hypotheses from the actual definition of `Ch07.admissible`, including off-by-one conventions.
4. **Residual non-vacuity:** independently evaluate `h=2`, source/intermediate cutoffs zero and target cutoff one, identifying the expected `−1/4` coefficient on the R-hole/L-sea configuration; check that the same projected residual vanishes at `Kt=0`. A source ground-to-ground amplitude alone does **not** justify dropping the residual on every vector or every target budget.
5. **Klein duality and character phase:** prove both `P_R(fN)=P_R(N)` and `P_L(fN)=-P_L(N+e_L)` for an arbitrary linear-order species set, including `L<R`; verify the `χ(1,x)` multiplier and complex `star` on the shifted **reverse** coefficient, not on the forward unshifted target. Check the norm-one laws use primitive canonical root with `0<h`, not an arbitrary twist.
6. **Parameter and family alignment:** confirm `dualParams.match_v2` elaborates with the exact A07 field equation; prove `dualParams` coordinatewise involutive, explicitly accounting for the dependent output index `-(-v2)`; do not identify different indexed records by definitional equality. Check `chiralPhaseOf` positive-mode sum reproduces orientation signs and dressed labels, `pairingModeOf` uses A07's same ordered products, `dual_commutator` has the cross-minus sign, and phase/X duality is the negative φ↔θ convention rather than a direct swap.
7. **Zero-mode and nonzero tests:** inspect `Ch17.zero_mode_scalar_canonical_mu` at `h=0` separately from its physical `0<h` regime, and verify the source/target scalar equality at canonical chemical potential only. Evaluate the explicit unadjusted μ energies (π−1 vs. 1), and verify `h=8,m=1,M=1` satisfies the hypotheses of `A07Interactions.pairing_mode_ground_nonzero` before treating that lemma as a nonzero witness for the pairing difference.
8. **Kernel and deferred scope:** verify the type and casts in the real finite `logKernel`, the denominator behavior at `h=0`, positivity for `m≥1`, and the `h=2,M=1,x−y=1` value. Do not import an unreviewed A08 carrier or state, claim `W_J` as a finite CAR operator, eliminate formal residuals, or assert finite-Fock/unitary/T-duality equivalence.
9. **Acceptance gate:** run the packet's `scripts/webllm/verify_phase_a.py` only inside the local repository, using the exact immutable baseline and after confirming `Bosonize.Core.Ch18Bogoliubov` has been promoted. Its successful elaboration would check the *interfaces*, not the mathematics: every lemma/theorem above remains an explicit `:= by sorry`, subject to independent mathematical review and the separate Phase B proof cycle. No compilation, execution, test, proof, or audit result is claimed here.
