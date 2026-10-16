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
    dualPair (dualPair hp) = hp := by
  cases hp
  simp [dualPair]

/-- Indexed parameter records have different syntactic fibers; state involution
on the physical coordinates rather than an ill-typed heterogeneous equality. -/
lemma dualParams_involutive {v1 v2 : ℝ}
    (lp : A07Interactions.HyperbolicParams v1 v2) :
    (dualParams (dualParams lp)).u = lp.u ∧
    (dualParams (dualParams lp)).c = lp.c ∧
    (dualParams (dualParams lp)).s = lp.s := by
  simp [dualParams]

lemma luttingerG_dual (hp : Ch18.HyperbolicPair) :
    Ch18.luttingerG (dualPair hp) = Ch18.luttingerGInv hp := by
  simp [Ch18.luttingerG, Ch18.luttingerGInv, dualPair]
  ring

lemma luttingerGInv_dual (hp : Ch18.HyperbolicPair) :
    Ch18.luttingerGInv (dualPair hp) = Ch18.luttingerG hp := by
  simp [Ch18.luttingerG, Ch18.luttingerGInv, dualPair]
  ring

lemma dualParams_pair {v1 v2 : ℝ}
    (lp : A07Interactions.HyperbolicParams v1 v2) :
    Ch18.HyperbolicPair.ofParams (dualParams lp) =
      dualPair (Ch18.HyperbolicPair.ofParams lp) := by
  cases lp with
  | mk u c s up cp us hid mv1 mv2 =>
    simp [dualParams, Ch18.HyperbolicPair.ofParams, dualPair]

lemma v2Velocity_neg (g2 : ℝ) :
    Ch17.v2Velocity (-g2) = -Ch17.v2Velocity g2 := by
  simp [Ch17.v2Velocity]
  ring

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
    dualFamily (dualFamily ρ) = ρ := by
  funext η k
  cases η <;> simp [dualFamily]

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
    logKernel h M x x = 0 := by
  simp [logKernel]

lemma logKernel_symm (h M : ℕ) (x y : ℤ) :
    logKernel h M x y = logKernel h M y x := by
  unfold logKernel
  congr 1
  ext m
  congr 1
  ring

lemma logKernel_nonneg (h M : ℕ) (x y : ℤ) :
    0 ≤ logKernel h M x y := by
  unfold logKernel
  apply Finset.sum_nonneg
  intro m hm
  apply div_nonneg
  · nlinarith [Real.cos_le_one (((2 * Real.pi * (m : ℝ) * ((x - y : ℤ) : ℝ)) / ((2 * h : ℕ) : ℝ)))]
  · exact Nat.cast_nonneg m

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
