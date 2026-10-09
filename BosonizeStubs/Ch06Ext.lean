module

public import Bosonize.Core.Ch06LocalNet
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# CH06 extension: scalar boundary holonomy and covariant ring transport
Phase A: complete data and one-sorry review contracts.
External scalar twists are independent of fermionic grading. Integer lifts expose the seam.
-/

@[expose] public section

namespace Bosonize.Ch06Ext

open scoped BigOperators Classical

/-- A chosen unit per-site phase, including a choice of root/trivialization at length L. -/
structure BoundaryTwist (L : ℕ) where
  step : ℂ
  norm_step : ‖step‖ = 1

/-- All external offset angles are allowed; β is measured in momentum-label units. -/
noncomputable def angleTwist (L : ℕ) (β : ℝ) : BoundaryTwist L :=
  ⟨Complex.exp (((2*Real.pi*β/(L : ℝ) : ℝ) : ℂ)*Complex.I),
    Complex.norm_exp_ofReal_mul_I _⟩

def periodicTwist (L : ℕ) : BoundaryTwist L := ⟨1, norm_one⟩

/-- Centered half-integer momenta use β=-1/2 in the existing positive-Nyquist labels. -/
noncomputable def antiperiodicTwist (L : ℕ) : BoundaryTwist L := angleTwist L (-1/2)

def holonomy (L : ℕ) (b : BoundaryTwist L) : ℂ := b.step^L

noncomputable def liftPhase (L : ℕ) (b : BoundaryTwist L) (n : ℤ) : ℂ := b.step^n

/-- A full-period phase does not specify the selected per-site root. -/
def sameHolonomy (L : ℕ) (b c : BoundaryTwist L) : Prop := holonomy L b = holonomy L c

section Fields
variable (L : ℕ) [NeZero L]

/-- Lift to ℤ; this is not asserted to descend to a periodic scalar-valued quotient field. -/
noncomputable def annihilation (b : BoundaryTwist L) (n : ℤ) : Ch05.Operators L :=
  liftPhase L b n • Ch05.positionAnnihilation L (n : Ch01.Lattice L)

noncomputable def creation (b : BoundaryTwist L) (n : ℤ) : Ch05.Operators L :=
  star (liftPhase L b n) • Ch05.positionCreation L (n : Ch01.Lattice L)

noncomputable def siteAnnihilation (b : BoundaryTwist L) (x : Ch01.Lattice L) : Ch05.Operators L :=
  annihilation L b (x.val : ℤ)

noncomputable def siteCreation (b : BoundaryTwist L) (x : Ch01.Lattice L) : Ch05.Operators L :=
  creation L b (x.val : ℤ)

noncomputable def density (b : BoundaryTwist L) (n : ℤ) : Ch05.Operators L :=
  creation L b n * annihilation L b n

/-- The actual kernel, with integer powers and the chosen external per-site phase. -/
noncomputable def twistedCharacter (b : BoundaryTwist L) (k : Ch01.Band L) (n : ℤ) : ℂ :=
  liftPhase L b n * A01.integerCharacter (A01.canonicalRoot L) k.val n

noncomputable def localGenerators (b : BoundaryTwist L) (I : Ch06.Region L) : Set (Ch05.Operators L) :=
  {A | ∃ x ∈ I, A = siteAnnihilation L b x ∨ A = siteCreation L b x}

noncomputable def localAlgebra (b : BoundaryTwist L) (I : Ch06.Region L) : Subalgebra ℂ (Ch05.Operators L) :=
  Algebra.adjoin ℂ (localGenerators L b I)

noncomputable def localPart (b : BoundaryTwist L) (I : Ch06.Region L) (σ : Ch06.Degree) :
    Submodule ℂ (Ch05.Operators L) :=
  (localAlgebra L b I).toSubmodule ⊓
    LinearMap.ker (Ch06.parityMap L - Ch06.degreeSign σ • LinearMap.id)

/-- Translation by m sites. The minus signs ensure positive-kernel annihilator covariance. -/
noncomputable def translation (b : BoundaryTwist L) (m : ℤ) : Ch05.Operators L :=
  A02.extendBasis (fun S =>
    (b.step^(-m*(S.card : ℤ)) *
      A01.canonicalRoot L^(-m*Ch05.occupationEnergy L S)) • A02.ket S)

noncomputable def gauge (u : ℂ) : Ch05.Operators L :=
  A02.extendBasis (fun S => u^(-(S.card : ℤ)) • A02.ket S)

noncomputable def transport (b : BoundaryTwist L) (m : ℤ) :
    Ch05.Operators L →ₗ[ℂ] Ch05.Operators L :=
  (LinearMap.mulRight ℂ (translation L b (-m))).comp
    (LinearMap.mulLeft ℂ (translation L b m))

def windingNumber (n : ℤ) : ℤ := n / (L : ℤ)

noncomputable def seamPhase (b : BoundaryTwist L) (n : ℤ) : ℂ :=
  holonomy L b ^ windingNumber L n

def shiftRegion (m : ℤ) (I : Ch06.Region L) : Ch06.Region L :=
  (fun x : Ch01.Lattice L => x+(m : Ch01.Lattice L)) '' I

/-- Source-sector phase for later Klein/vertex constructions; no field equality is assumed. -/
noncomputable def zeroMode (b : BoundaryTwist L) (n : ℤ) (referenceCharge : ℤ) : Ch05.Operators L :=
  A02.extendBasis (fun S =>
    (liftPhase L b n * A01.canonicalRoot L^(n*((S.card : ℤ)-referenceCharge))) • A02.ket S)

lemma twist_step_ne_zero (b : BoundaryTwist L) : b.step ≠ 0 := by sorry
lemma holonomy_norm (b : BoundaryTwist L) : ‖holonomy L b‖ = 1 := by sorry
lemma lift_phase_norm (b : BoundaryTwist L) (n : ℤ) : ‖liftPhase L b n‖ = 1 := by sorry
lemma lift_phase_add (b : BoundaryTwist L) (n m : ℤ) :
    liftPhase L b (n+m) = liftPhase L b n * liftPhase L b m := by sorry
lemma lift_phase_winding (b : BoundaryTwist L) (n w : ℤ) :
    liftPhase L b (n+w*(L : ℤ)) = holonomy L b^w * liftPhase L b n := by sorry
lemma angle_holonomy (β : ℝ) :
    holonomy L (angleTwist L β) = Complex.exp (((2*Real.pi*β : ℝ) : ℂ)*Complex.I) := by sorry
lemma angle_twist_surjective (b : BoundaryTwist L) : ∃ β : ℝ, angleTwist L β = b := by sorry
lemma holonomy_surjective (u : ℂ) (hu : ‖u‖ = 1) :
    ∃ b : BoundaryTwist L, holonomy L b = u := by sorry
lemma periodic_holonomy : holonomy L (periodicTwist L) = 1 := by sorry
lemma antiperiodic_holonomy : holonomy L (antiperiodicTwist L) = -1 := by sorry
lemma angle_integer_holonomy (β : ℝ) (z : ℤ) :
    sameHolonomy L (angleTwist L (β+(z : ℝ))) (angleTwist L β) := by sorry
lemma angle_root_shift (β : ℝ) :
    (angleTwist L (β+1)).step = (angleTwist L β).step * A01.canonicalRoot L := by sorry

lemma winding_decomposition (n : ℤ) :
    n = (((n : Ch01.Lattice L).val : ℕ) : ℤ)+windingNumber L n*(L : ℤ) := by sorry
lemma seam_phase_winding (b : BoundaryTwist L) (n w : ℤ) :
    seamPhase L b (n+w*(L : ℤ)) = holonomy L b^w*seamPhase L b n := by sorry
lemma twisted_character_orthogonality (b : BoundaryTwist L) (k p : Ch01.Band L) :
    (∑ x : Ch01.Lattice L,
      star (twistedCharacter L b k (x.val : ℤ))*twistedCharacter L b p (x.val : ℤ)) =
      if k=p then (L : ℂ) else 0 := by sorry
lemma twisted_fourier_inverse (b : BoundaryTwist L) (k : Ch01.Band L) :
    Ch05.momentumAnnihilation L k = (A01.normalization L : ℂ) •
      ∑ x : Ch01.Lattice L, star (twistedCharacter L b k (x.val : ℤ)) •
        siteAnnihilation L b x := by sorry

lemma annihilation_fourier (b : BoundaryTwist L) (n : ℤ) :
    annihilation L b n = (A01.normalization L : ℂ) •
      ∑ k : Ch01.Band L, twistedCharacter L b k n • Ch05.momentumAnnihilation L k := by sorry
lemma creation_adjoint (b : BoundaryTwist L) (n : ℤ) :
    creation L b n = LinearMap.adjoint (annihilation L b n) := by sorry
lemma annihilation_winding (b : BoundaryTwist L) (n w : ℤ) :
    annihilation L b (n+w*(L : ℤ)) = holonomy L b^w • annihilation L b n := by sorry
lemma creation_winding (b : BoundaryTwist L) (n w : ℤ) :
    creation L b (n+w*(L : ℤ)) = star (holonomy L b^w) • creation L b n := by sorry
lemma lift_site_relation (b : BoundaryTwist L) (n : ℤ) :
    annihilation L b n = seamPhase L b n • siteAnnihilation L b (n : Ch01.Lattice L) := by sorry
lemma periodic_field (n : ℤ) :
    annihilation L (periodicTwist L) n = Ch05.positionAnnihilation L (n : Ch01.Lattice L) := by sorry
lemma antiperiodic_field (n : ℤ) :
    annihilation L (antiperiodicTwist L) (n+(L : ℤ)) = -annihilation L (antiperiodicTwist L) n := by sorry
lemma annihilation_ne_zero (b : BoundaryTwist L) (n : ℤ) : annihilation L b n ≠ 0 := by sorry
lemma quotient_descent_iff (b : BoundaryTwist L) :
    (∃ f : Ch01.Lattice L → Ch05.Operators L, ∀ n : ℤ, annihilation L b n = f (n : Ch01.Lattice L)) ↔
      holonomy L b = 1 := by sorry
lemma site_annihilation_car (b : BoundaryTwist L) (x y : Ch01.Lattice L) :
    A02.anticommutator (siteAnnihilation L b x) (siteAnnihilation L b y) = 0 := by sorry
lemma site_creation_car (b : BoundaryTwist L) (x y : Ch01.Lattice L) :
    A02.anticommutator (siteCreation L b x) (siteCreation L b y) = 0 := by sorry
lemma site_mixed_car (b : BoundaryTwist L) (x y : Ch01.Lattice L) :
    A02.anticommutator (siteAnnihilation L b x) (siteCreation L b y) =
      (if x=y then (1 : ℂ) else 0) • (1 : Ch05.Operators L) := by sorry
lemma lifted_mixed_car (b : BoundaryTwist L) (n m : ℤ) :
    A02.anticommutator (annihilation L b n) (creation L b m) =
      (if (n : Ch01.Lattice L)=(m : Ch01.Lattice L) then liftPhase L b (n-m) else 0) •
        (1 : Ch05.Operators L) := by sorry
lemma density_untwisted (b : BoundaryTwist L) (n : ℤ) :
    density L b n = Ch05.positionNumber L (n : Ch01.Lattice L) := by sorry
lemma density_periodic (b : BoundaryTwist L) (n : ℤ) : density L b (n+(L : ℤ)) = density L b n := by sorry
lemma local_algebra_eq (b : BoundaryTwist L) (I : Ch06.Region L) : localAlgebra L b I = Ch06.localAlgebra L I := by sorry
lemma local_part_eq (b : BoundaryTwist L) (I : Ch06.Region L) (σ : Ch06.Degree) :
    localPart L b I σ = Ch06.localPart L I σ := by sorry
lemma graded_locality (b : BoundaryTwist L) (I J : Ch06.Region L) (hIJ : Disjoint I J)
    (σ τ : Ch06.Degree) (A B : Ch05.Operators L)
    (hA : A ∈ localPart L b I σ) (hB : B ∈ localPart L b J τ) :
    A*B = (-1 : ℂ)^(σ.val*τ.val) • (B*A) := by sorry

lemma translation_ket (b : BoundaryTwist L) (m : ℤ) (S : Ch06.Occupation L) :
    translation L b m (A02.ket S) =
      (b.step^(-m*(S.card : ℤ))*A01.canonicalRoot L^(-m*Ch05.occupationEnergy L S)) • A02.ket S := by sorry
lemma translation_zero (b : BoundaryTwist L) : translation L b 0 = 1 := by sorry
lemma translation_add (b : BoundaryTwist L) (m n : ℤ) :
    translation L b (m+n) = translation L b m * translation L b n := by sorry
lemma translation_adjoint (b : BoundaryTwist L) (m : ℤ) :
    LinearMap.adjoint (translation L b m) = translation L b (-m) := by sorry
lemma translation_unitary (b : BoundaryTwist L) (m : ℤ) :
    translation L b m * LinearMap.adjoint (translation L b m) = 1 ∧
      LinearMap.adjoint (translation L b m) * translation L b m = 1 := by sorry
lemma transport_apply (b : BoundaryTwist L) (m : ℤ) (A : Ch05.Operators L) :
    transport L b m A = translation L b m*A*translation L b (-m) := by sorry
lemma transport_add (b : BoundaryTwist L) (m n : ℤ) (A : Ch05.Operators L) :
    transport L b (m+n) A = transport L b m (transport L b n A) := by sorry
lemma transport_star (b : BoundaryTwist L) (m : ℤ) (A : Ch05.Operators L) :
    transport L b m (LinearMap.adjoint A) = LinearMap.adjoint (transport L b m A) := by sorry
lemma transport_automorphism_exists (b : BoundaryTwist L) (m : ℤ) :
    ∃ f : Ch05.Operators L ≃ₐ[ℂ] Ch05.Operators L,
      (∀ A, f A = transport L b m A) ∧
      ∀ A, f (LinearMap.adjoint A) = LinearMap.adjoint (f A) := by sorry
lemma transport_annihilation (b : BoundaryTwist L) (m n : ℤ) :
    transport L b m (annihilation L b n) = annihilation L b (n+m) := by sorry
lemma transport_creation (b : BoundaryTwist L) (m n : ℤ) :
    transport L b m (creation L b n) = creation L b (n+m) := by sorry
lemma site_transport (b : BoundaryTwist L) (m : ℤ) (x : Ch01.Lattice L) :
    transport L b m (siteAnnihilation L b x) =
      seamPhase L b ((x.val : ℤ)+m) • siteAnnihilation L b (x+(m : Ch01.Lattice L)) := by sorry
lemma seam_transport (b : BoundaryTwist L) :
    transport L b 1 (annihilation L b ((L : ℤ)-1)) = holonomy L b • annihilation L b 0 := by sorry
lemma local_transport (b : BoundaryTwist L) (m : ℤ) (I : Ch06.Region L) :
    ∀ A, A ∈ localAlgebra L b I ↔ transport L b m A ∈ localAlgebra L b (shiftRegion L m I) := by sorry
lemma local_part_transport (b : BoundaryTwist L) (m : ℤ) (I : Ch06.Region L) (σ : Ch06.Degree) :
    ∀ A, A ∈ localPart L b I σ ↔ transport L b m A ∈ localPart L b (shiftRegion L m I) σ := by sorry
lemma translation_preserves_number (b : BoundaryTwist L) (m : ℤ) :
    transport L b m (Ch05.totalNumber L) = Ch05.totalNumber L := by sorry
lemma translation_preserves_hamiltonian (b : BoundaryTwist L) (m : ℤ) :
    transport L b m (Ch05.bareHamiltonian L) = Ch05.bareHamiltonian L := by sorry
lemma translation_preserves_parity (b : BoundaryTwist L) (m : ℤ) :
    transport L b m (Ch06.parityOperator L) = Ch06.parityOperator L := by sorry
lemma full_ring_translation (b : BoundaryTwist L) :
    translation L b (L : ℤ) = gauge L (holonomy L b) := by sorry
lemma translation_power (b : BoundaryTwist L) (m : ℕ) :
    translation L b (m : ℤ) = translation L b 1 ^ m := by sorry
lemma apbc_full_ring_parity :
    translation L (antiperiodicTwist L) (L : ℤ) = Ch06.parityOperator L := by sorry
lemma holonomy_acts_on_field (b : BoundaryTwist L) (n : ℤ) :
    transport L b (L : ℤ) (annihilation L b n) = holonomy L b • annihilation L b n := by sorry
lemma holonomy_detected_iff (b c : BoundaryTwist L) :
    (∀ n : ℤ, transport L b (L : ℤ) (annihilation L b n) =
      holonomy L c • annihilation L b n) ↔ sameHolonomy L b c := by sorry
lemma change_trivialization_field (b c : BoundaryTwist L) (n : ℤ) :
    annihilation L c n = (c.step/b.step)^n • annihilation L b n := by sorry
lemma trivialization_ratio_periodic (b c : BoundaryTwist L) (hbc : sameHolonomy L b c) (n : ℤ) :
    (c.step/b.step)^(n+(L : ℤ)) = (c.step/b.step)^n := by sorry
lemma zero_mode_ket (b : BoundaryTwist L) (n referenceCharge : ℤ) (S : Ch06.Occupation L) :
    zeroMode L b n referenceCharge (A02.ket S) =
      (liftPhase L b n*A01.canonicalRoot L^(n*((S.card : ℤ)-referenceCharge))) • A02.ket S := by sorry
lemma zero_mode_winding (b : BoundaryTwist L) (n referenceCharge w : ℤ) :
    zeroMode L b (n+w*(L : ℤ)) referenceCharge = holonomy L b^w • zeroMode L b n referenceCharge := by sorry
lemma zero_mode_unitary (b : BoundaryTwist L) (n referenceCharge : ℤ) :
    LinearMap.adjoint (zeroMode L b n referenceCharge)*zeroMode L b n referenceCharge = 1 := by sorry
lemma zero_mode_creation_order (b : BoundaryTwist L) (n referenceCharge : ℤ) (k : Ch01.Band L) :
    zeroMode L b n referenceCharge*Ch05.momentumCreation L k =
      A01.canonicalRoot L^n • (Ch05.momentumCreation L k*zeroMode L b n referenceCharge) := by sorry
lemma zero_mode_annihilation_order (b : BoundaryTwist L) (n referenceCharge : ℤ) (k : Ch01.Band L) :
    zeroMode L b n referenceCharge*Ch05.momentumAnnihilation L k =
      A01.canonicalRoot L^(-n) • (Ch05.momentumAnnihilation L k*zeroMode L b n referenceCharge) := by sorry

end Fields

/-- A separate source-sector boundary dictionary; not a fixed-flux field identity. -/
noncomputable def jwHolonomy (particles : ℤ) : ℂ := -((-1 : ℂ)^particles)

noncomputable def jwSectorTwist (L : ℕ) (particles : ℤ) : BoundaryTwist L :=
  if Even particles then antiperiodicTwist L else periodicTwist L

lemma jw_even (particles : ℤ) (hp : Even particles) : jwHolonomy particles = -1 := by sorry
lemma jw_odd (particles : ℤ) (hp : Odd particles) : jwHolonomy particles = 1 := by sorry
lemma jw_sector_holonomy (L : ℕ) [NeZero L] (particles : ℤ) :
    holonomy L (jwSectorTwist L particles) = jwHolonomy particles := by sorry
lemma jw_parity_flip (particles : ℤ) : jwHolonomy (particles-1) = -jwHolonomy particles := by sorry

/-- Physical linear-dispersion labels require an offset, not merely its boundary phase. -/
def physicalMomentum (L : ℕ) (β : ℝ) (k : Ch01.Band L) : ℝ := (k.val : ℝ)+β

def physicalOccupationEnergy (L : ℕ) (β : ℝ) (S : Ch06.Occupation L) : ℝ :=
  ∑ k ∈ S, physicalMomentum L β k

def physicalRelativeEnergy (L : ℕ) (β : ℝ) (S : Ch06.Occupation L) : ℝ :=
  physicalOccupationEnergy L β S - physicalOccupationEnergy L β (Ch05.seaConfiguration L)

noncomputable def physicalGroundEnergy (β : ℝ) (N : ℤ) : ℝ := (N : ℝ)*((N : ℝ)+1)/2+β*(N : ℝ)

lemma physical_energy_shift (L : ℕ) (β : ℝ) (S : Ch06.Occupation L) :
    physicalOccupationEnergy L β S = (Ch05.occupationEnergy L S : ℝ)+β*(S.card : ℝ) := by sorry
lemma physical_relative_shift (L : ℕ) (β : ℝ) (S : Ch06.Occupation L) :
    physicalRelativeEnergy L β S =
      ((Ch05.occupationEnergy L S-Ch05.seaEnergy L : ℤ) : ℝ)+
      β*((S.card : ℝ)-((Ch05.seaConfiguration L).card : ℝ)) := by sorry
lemma excitation_twist_cancel (h : ℕ) (hh : 0 < h) (β : ℝ) (S : Ch06.Occupation (2*h)) :
    physicalRelativeEnergy (2*h) β S-physicalGroundEnergy β ((S.card : ℤ)-(h : ℤ)) =
      ((Ch05.occupationEnergy (2*h) S-Ch05.seaEnergy (2*h) : ℤ) : ℝ)-
        physicalGroundEnergy 0 ((S.card : ℤ)-(h : ℤ)) := by sorry
lemma apbc_ground_energy (N : ℤ) : physicalGroundEnergy (-1/2) N = (N : ℝ)^2/2 := by sorry

end Bosonize.Ch06Ext
