import Bosonize.Core.Ch18Bogoliubov
import Bosonize.Core.A08OscillatorStates

namespace Bosonize.Ch19

open scoped BigOperators

noncomputable def densityKernel (h M : ℕ) (ζ : ℂ) (c2 s2 : ℝ) (d : ℤ) : ℂ :=
  (((2 * h : ℕ) : ℂ)⁻¹) ^ 2 * ∑ m ∈ Finset.Icc 1 M, (m : ℂ) *
    ((s2 : ℂ) * Bosonize.A01.integerCharacter ζ (-(m : ℤ)) d +
     (c2 : ℂ) * Bosonize.A01.integerCharacter ζ (m : ℤ) d)

noncomputable def oscDensityR (h M : ℕ) (ζ : ℂ) (x : ZMod (2 * h)) : Bosonize.A08.OscAlgebra M :=
  (((2 * h : ℕ) : ℂ)⁻¹) • ∑ i : Fin M,
    (Bosonize.A06.latticeCharacter h ζ (-((i.val + 1 : ℕ) : ℤ)) x • Bosonize.A08.creatorGen M .right i +
     Bosonize.A06.latticeCharacter h ζ ((i.val + 1 : ℕ) : ℤ) x • Bosonize.A08.annihilatorGen M .right i)

noncomputable def orderedDensityCorrelation (h M : ℕ) (ζ : ℂ) (hp : Bosonize.Ch18.HyperbolicPair) (x y : ZMod (2 * h)) : ℂ :=
  Bosonize.A08.omegaP M hp (oscDensityR h M ζ x * oscDensityR h M ζ y)

def freePair : Bosonize.Ch18.HyperbolicPair :=
  ⟨1, 0, by norm_num⟩

theorem omegaP_creator_annihilator_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.creatorGen M .right i * Bosonize.A08.annihilatorGen M .right j) =
      if i = j then ((i.val + 1 : ℕ) : ℂ) * (hp.s : ℂ) ^ 2 else 0 := by
  open Bosonize.A08 in
  have hrep_cre :
      oscRep M (bogoliubovMap M hp.c (-hp.s) (creatorGen M .right i)) =
        (hp.c : ℂ) • oscCreation M (.right, i) +
        (-hp.s : ℂ) • oscAnnihilation M (.left, i) := by
    dsimp [bogoliubovMap, oscRep, creatorGen]
    rw [FreeAlgebra.lift_ι_apply, ← Complex.coe_smul hp.c, ← Complex.coe_smul (-hp.s)]
    simp only [map_add, map_smul, FreeAlgebra.lift_ι_apply, Bool.not_true]
    push_cast
    rfl
  open Bosonize.A08 in
  have hrep_ann :
      oscRep M (bogoliubovMap M hp.c (-hp.s) (annihilatorGen M .right j)) =
        (hp.c : ℂ) • oscAnnihilation M (.right, j) +
        (-hp.s : ℂ) • oscCreation M (.left, j) := by
    dsimp [bogoliubovMap, oscRep, annihilatorGen]
    rw [FreeAlgebra.lift_ι_apply, ← Complex.coe_smul hp.c, ← Complex.coe_smul (-hp.s)]
    simp only [map_add, map_smul, FreeAlgebra.lift_ι_apply, Bool.not_false]
    push_cast
    rfl
  open Bosonize.A08 in
  have ann_X (p q : OscMode M) :
      oscAnnihilation M p (MvPolynomial.X q) = if p = q then (oscWeight p : ℂ) • (1 : OscPoly M) else 0 := by
    dsimp [oscAnnihilation]
    by_cases h : p = q
    · subst h
      simp [MvPolynomial.pderiv_X]
    · simp [MvPolynomial.pderiv_X_of_ne (Ne.symm h), h]
  have ccoeff_zero (p : Bosonize.A08.OscPoly M) : (MvPolynomial.lcoeff ℂ 0) p = MvPolynomial.constantCoeff p := rfl
  open Bosonize.A08 in
  have ccoeff_cre (p : OscMode M) (y : OscPoly M) :
      MvPolynomial.constantCoeff (oscCreation M p y) = 0 := by
    dsimp [oscCreation]
    rw [map_mul, MvPolynomial.constantCoeff_X, zero_mul]
  dsimp [Bosonize.A08.omegaP, Bosonize.A08.omega0]
  rw [ccoeff_zero, map_mul, map_mul]
  simp only [LinearMap.applyₗ_apply_apply, Module.End.mul_apply]
  rw [hrep_ann]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Bosonize.A08.oscAnnihilation_one, smul_zero, zero_add]
  have hcre_one : Bosonize.A08.oscCreation M (.left, j) 1 = MvPolynomial.X (.left, j) := by
    simp [Bosonize.A08.oscCreation]
  rw [hcre_one, hrep_cre]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [map_add, MvPolynomial.constantCoeff_smul, ccoeff_cre, smul_zero, zero_add,
    MvPolynomial.constantCoeff_smul, map_smul, MvPolynomial.constantCoeff_smul, ann_X]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true, MvPolynomial.constantCoeff_smul, map_one, smul_eq_mul, mul_one]
    dsimp [Bosonize.A08.oscWeight]
    ring
  · have hne : (Bosonize.A06.Orientation.left, i) ≠ (Bosonize.A06.Orientation.left, j) := by
      intro h; cases h; exact hij rfl
    simp [hne, hij]

theorem omegaP_annihilator_creator_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.annihilatorGen M .right i * Bosonize.A08.creatorGen M .right j) =
      if i = j then ((i.val + 1 : ℕ) : ℂ) * (hp.c : ℂ) ^ 2 else 0 := by
  open Bosonize.A08 in
  have hrep_cre :
      oscRep M (bogoliubovMap M hp.c (-hp.s) (creatorGen M .right j)) =
        (hp.c : ℂ) • oscCreation M (.right, j) +
        (-hp.s : ℂ) • oscAnnihilation M (.left, j) := by
    dsimp [bogoliubovMap, oscRep, creatorGen]
    rw [FreeAlgebra.lift_ι_apply, ← Complex.coe_smul hp.c, ← Complex.coe_smul (-hp.s)]
    simp only [map_add, map_smul, FreeAlgebra.lift_ι_apply, Bool.not_true]
    push_cast
    rfl
  open Bosonize.A08 in
  have hrep_ann :
      oscRep M (bogoliubovMap M hp.c (-hp.s) (annihilatorGen M .right i)) =
        (hp.c : ℂ) • oscAnnihilation M (.right, i) +
        (-hp.s : ℂ) • oscCreation M (.left, i) := by
    dsimp [bogoliubovMap, oscRep, annihilatorGen]
    rw [FreeAlgebra.lift_ι_apply, ← Complex.coe_smul hp.c, ← Complex.coe_smul (-hp.s)]
    simp only [map_add, map_smul, FreeAlgebra.lift_ι_apply, Bool.not_false]
    push_cast
    rfl
  open Bosonize.A08 in
  have ann_X (p q : OscMode M) :
      oscAnnihilation M p (MvPolynomial.X q) = if p = q then (oscWeight p : ℂ) • (1 : OscPoly M) else 0 := by
    dsimp [oscAnnihilation]
    by_cases h : p = q
    · subst h
      simp [MvPolynomial.pderiv_X]
    · simp [MvPolynomial.pderiv_X_of_ne (Ne.symm h), h]
  have ccoeff_zero (p : Bosonize.A08.OscPoly M) : (MvPolynomial.lcoeff ℂ 0) p = MvPolynomial.constantCoeff p := rfl
  open Bosonize.A08 in
  have ccoeff_cre (p : OscMode M) (y : OscPoly M) :
      MvPolynomial.constantCoeff (oscCreation M p y) = 0 := by
    dsimp [oscCreation]
    rw [map_mul, MvPolynomial.constantCoeff_X, zero_mul]
  dsimp [Bosonize.A08.omegaP, Bosonize.A08.omega0]
  rw [ccoeff_zero, map_mul, map_mul]
  simp only [LinearMap.applyₗ_apply_apply, Module.End.mul_apply]
  rw [hrep_cre]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Bosonize.A08.oscAnnihilation_one, smul_zero, add_zero]
  have hcre_one : Bosonize.A08.oscCreation M (.right, j) 1 = MvPolynomial.X (.right, j) := by
    simp [Bosonize.A08.oscCreation]
  rw [hcre_one, hrep_ann]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [map_add, MvPolynomial.constantCoeff_smul, map_smul, MvPolynomial.constantCoeff_smul, ann_X,
    MvPolynomial.constantCoeff_smul, ccoeff_cre, smul_zero, add_zero]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true, MvPolynomial.constantCoeff_smul, map_one, smul_eq_mul, mul_one]
    dsimp [Bosonize.A08.oscWeight]
    ring
  · have hne : (Bosonize.A06.Orientation.right, i) ≠ (Bosonize.A06.Orientation.right, j) := by
      intro h; cases h; exact hij rfl
    simp [hne, hij]

theorem omegaP_creator_creator_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.creatorGen M .right i * Bosonize.A08.creatorGen M .right j) = 0 := by
  open Bosonize.A08 in
  have hrep_cre (k : Fin M) :
      oscRep M (bogoliubovMap M hp.c (-hp.s) (creatorGen M .right k)) =
        (hp.c : ℂ) • oscCreation M (.right, k) +
        (-hp.s : ℂ) • oscAnnihilation M (.left, k) := by
    dsimp [bogoliubovMap, oscRep, creatorGen]
    rw [FreeAlgebra.lift_ι_apply, ← Complex.coe_smul hp.c, ← Complex.coe_smul (-hp.s)]
    simp only [map_add, map_smul, FreeAlgebra.lift_ι_apply, Bool.not_true]
    push_cast
    rfl
  open Bosonize.A08 in
  have ann_X (p q : OscMode M) :
      oscAnnihilation M p (MvPolynomial.X q) = if p = q then (oscWeight p : ℂ) • (1 : OscPoly M) else 0 := by
    dsimp [oscAnnihilation]
    by_cases h : p = q
    · subst h
      simp [MvPolynomial.pderiv_X]
    · simp [MvPolynomial.pderiv_X_of_ne (Ne.symm h), h]
  have ccoeff_zero (p : Bosonize.A08.OscPoly M) : (MvPolynomial.lcoeff ℂ 0) p = MvPolynomial.constantCoeff p := rfl
  open Bosonize.A08 in
  have ccoeff_cre (p : OscMode M) (y : OscPoly M) :
      MvPolynomial.constantCoeff (oscCreation M p y) = 0 := by
    dsimp [oscCreation]
    rw [map_mul, MvPolynomial.constantCoeff_X, zero_mul]
  dsimp [Bosonize.A08.omegaP, Bosonize.A08.omega0]
  rw [ccoeff_zero, map_mul, map_mul]
  simp only [LinearMap.applyₗ_apply_apply, Module.End.mul_apply]
  rw [hrep_cre j]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Bosonize.A08.oscAnnihilation_one, smul_zero, add_zero]
  have hcre_one : Bosonize.A08.oscCreation M (.right, j) 1 = MvPolynomial.X (.right, j) := by
    simp [Bosonize.A08.oscCreation]
  rw [hcre_one, hrep_cre i]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [map_add, MvPolynomial.constantCoeff_smul, ccoeff_cre, smul_zero, zero_add,
    MvPolynomial.constantCoeff_smul, map_smul, MvPolynomial.constantCoeff_smul, ann_X]
  have hne : (Bosonize.A06.Orientation.left, i) ≠ (Bosonize.A06.Orientation.right, j) := by
    intro h; cases h
  simp [hne]

theorem omegaP_annihilator_annihilator_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.annihilatorGen M .right i * Bosonize.A08.annihilatorGen M .right j) = 0 := by
  open Bosonize.A08 in
  have hrep_ann (k : Fin M) :
      oscRep M (bogoliubovMap M hp.c (-hp.s) (annihilatorGen M .right k)) =
        (hp.c : ℂ) • oscAnnihilation M (.right, k) +
        (-hp.s : ℂ) • oscCreation M (.left, k) := by
    dsimp [bogoliubovMap, oscRep, annihilatorGen]
    rw [FreeAlgebra.lift_ι_apply, ← Complex.coe_smul hp.c, ← Complex.coe_smul (-hp.s)]
    simp only [map_add, map_smul, FreeAlgebra.lift_ι_apply, Bool.not_false]
    push_cast
    rfl
  open Bosonize.A08 in
  have ann_X (p q : OscMode M) :
      oscAnnihilation M p (MvPolynomial.X q) = if p = q then (oscWeight p : ℂ) • (1 : OscPoly M) else 0 := by
    dsimp [oscAnnihilation]
    by_cases h : p = q
    · subst h
      simp [MvPolynomial.pderiv_X]
    · simp [MvPolynomial.pderiv_X_of_ne (Ne.symm h), h]
  have ccoeff_zero (p : Bosonize.A08.OscPoly M) : (MvPolynomial.lcoeff ℂ 0) p = MvPolynomial.constantCoeff p := rfl
  open Bosonize.A08 in
  have ccoeff_cre (p : OscMode M) (y : OscPoly M) :
      MvPolynomial.constantCoeff (oscCreation M p y) = 0 := by
    dsimp [oscCreation]
    rw [map_mul, MvPolynomial.constantCoeff_X, zero_mul]
  dsimp [Bosonize.A08.omegaP, Bosonize.A08.omega0]
  rw [ccoeff_zero, map_mul, map_mul]
  simp only [LinearMap.applyₗ_apply_apply, Module.End.mul_apply]
  rw [hrep_ann j]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Bosonize.A08.oscAnnihilation_one, smul_zero, zero_add]
  have hcre_one : Bosonize.A08.oscCreation M (.left, j) 1 = MvPolynomial.X (.left, j) := by
    simp [Bosonize.A08.oscCreation]
  rw [hcre_one, hrep_ann i]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [map_add, MvPolynomial.constantCoeff_smul, map_smul, MvPolynomial.constantCoeff_smul, ann_X,
    MvPolynomial.constantCoeff_smul, ccoeff_cre, smul_zero, add_zero]
  have hne : (Bosonize.A06.Orientation.right, i) ≠ (Bosonize.A06.Orientation.left, j) := by
    intro h; cases h
  simp [hne]

theorem omegaP_cross_creator_creator (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.creatorGen M .right i * Bosonize.A08.creatorGen M .left j) =
      if i = j then -(((i.val + 1 : ℕ) : ℂ) * (hp.c : ℂ) * (hp.s : ℂ)) else 0 := by
  open Bosonize.A08 in
  have hrep_cre_left :
      oscRep M (bogoliubovMap M hp.c (-hp.s) (creatorGen M .left j)) =
        (hp.c : ℂ) • oscCreation M (.left, j) +
        (-hp.s : ℂ) • oscAnnihilation M (.right, j) := by
    dsimp [bogoliubovMap, oscRep, creatorGen]
    rw [FreeAlgebra.lift_ι_apply, ← Complex.coe_smul hp.c, ← Complex.coe_smul (-hp.s)]
    simp only [map_add, map_smul, FreeAlgebra.lift_ι_apply, Bool.not_true]
    push_cast
    rfl
  open Bosonize.A08 in
  have hrep_cre_right :
      oscRep M (bogoliubovMap M hp.c (-hp.s) (creatorGen M .right i)) =
        (hp.c : ℂ) • oscCreation M (.right, i) +
        (-hp.s : ℂ) • oscAnnihilation M (.left, i) := by
    dsimp [bogoliubovMap, oscRep, creatorGen]
    rw [FreeAlgebra.lift_ι_apply, ← Complex.coe_smul hp.c, ← Complex.coe_smul (-hp.s)]
    simp only [map_add, map_smul, FreeAlgebra.lift_ι_apply, Bool.not_true]
    push_cast
    rfl
  open Bosonize.A08 in
  have ann_X (p q : OscMode M) :
      oscAnnihilation M p (MvPolynomial.X q) = if p = q then (oscWeight p : ℂ) • (1 : OscPoly M) else 0 := by
    dsimp [oscAnnihilation]
    by_cases h : p = q
    · subst h
      simp [MvPolynomial.pderiv_X]
    · simp [MvPolynomial.pderiv_X_of_ne (Ne.symm h), h]
  have ccoeff_zero (p : Bosonize.A08.OscPoly M) : (MvPolynomial.lcoeff ℂ 0) p = MvPolynomial.constantCoeff p := rfl
  open Bosonize.A08 in
  have ccoeff_cre (p : OscMode M) (y : OscPoly M) :
      MvPolynomial.constantCoeff (oscCreation M p y) = 0 := by
    dsimp [oscCreation]
    rw [map_mul, MvPolynomial.constantCoeff_X, zero_mul]
  dsimp [Bosonize.A08.omegaP, Bosonize.A08.omega0]
  rw [ccoeff_zero, map_mul, map_mul]
  simp only [LinearMap.applyₗ_apply_apply, Module.End.mul_apply]
  rw [hrep_cre_left]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Bosonize.A08.oscAnnihilation_one, smul_zero, add_zero]
  have hcre_one : Bosonize.A08.oscCreation M (.left, j) 1 = MvPolynomial.X (.left, j) := by
    simp [Bosonize.A08.oscCreation]
  rw [hcre_one, hrep_cre_right]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [map_add, MvPolynomial.constantCoeff_smul, ccoeff_cre, smul_zero, zero_add,
    MvPolynomial.constantCoeff_smul, map_smul, MvPolynomial.constantCoeff_smul, ann_X]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true, MvPolynomial.constantCoeff_smul, map_one, smul_eq_mul, mul_one]
    dsimp [Bosonize.A08.oscWeight]
    ring
  · have hne : (Bosonize.A06.Orientation.left, i) ≠ (Bosonize.A06.Orientation.left, j) := by
      intro h; cases h; exact hij rfl
    simp [hne, hij]

theorem omegaP_cross_annihilator_annihilator (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.annihilatorGen M .right i * Bosonize.A08.annihilatorGen M .left j) =
      if i = j then -(((i.val + 1 : ℕ) : ℂ) * (hp.c : ℂ) * (hp.s : ℂ)) else 0 := by
  open Bosonize.A08 in
  have hrep_ann_left :
      oscRep M (bogoliubovMap M hp.c (-hp.s) (annihilatorGen M .left j)) =
        (hp.c : ℂ) • oscAnnihilation M (.left, j) +
        (-hp.s : ℂ) • oscCreation M (.right, j) := by
    dsimp [bogoliubovMap, oscRep, annihilatorGen]
    rw [FreeAlgebra.lift_ι_apply, ← Complex.coe_smul hp.c, ← Complex.coe_smul (-hp.s)]
    simp only [map_add, map_smul, FreeAlgebra.lift_ι_apply, Bool.not_false]
    push_cast
    rfl
  open Bosonize.A08 in
  have hrep_ann_right :
      oscRep M (bogoliubovMap M hp.c (-hp.s) (annihilatorGen M .right i)) =
        (hp.c : ℂ) • oscAnnihilation M (.right, i) +
        (-hp.s : ℂ) • oscCreation M (.left, i) := by
    dsimp [bogoliubovMap, oscRep, annihilatorGen]
    rw [FreeAlgebra.lift_ι_apply, ← Complex.coe_smul hp.c, ← Complex.coe_smul (-hp.s)]
    simp only [map_add, map_smul, FreeAlgebra.lift_ι_apply, Bool.not_false]
    push_cast
    rfl
  open Bosonize.A08 in
  have ann_X (p q : OscMode M) :
      oscAnnihilation M p (MvPolynomial.X q) = if p = q then (oscWeight p : ℂ) • (1 : OscPoly M) else 0 := by
    dsimp [oscAnnihilation]
    by_cases h : p = q
    · subst h
      simp [MvPolynomial.pderiv_X]
    · simp [MvPolynomial.pderiv_X_of_ne (Ne.symm h), h]
  have ccoeff_zero (p : Bosonize.A08.OscPoly M) : (MvPolynomial.lcoeff ℂ 0) p = MvPolynomial.constantCoeff p := rfl
  open Bosonize.A08 in
  have ccoeff_cre (p : OscMode M) (y : OscPoly M) :
      MvPolynomial.constantCoeff (oscCreation M p y) = 0 := by
    dsimp [oscCreation]
    rw [map_mul, MvPolynomial.constantCoeff_X, zero_mul]
  dsimp [Bosonize.A08.omegaP, Bosonize.A08.omega0]
  rw [ccoeff_zero, map_mul, map_mul]
  simp only [LinearMap.applyₗ_apply_apply, Module.End.mul_apply]
  rw [hrep_ann_left]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Bosonize.A08.oscAnnihilation_one, smul_zero, zero_add]
  have hcre_one : Bosonize.A08.oscCreation M (.right, j) 1 = MvPolynomial.X (.right, j) := by
    simp [Bosonize.A08.oscCreation]
  rw [hcre_one, hrep_ann_right]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [map_add, MvPolynomial.constantCoeff_smul, map_smul, MvPolynomial.constantCoeff_smul, ann_X,
    MvPolynomial.constantCoeff_smul, ccoeff_cre, smul_zero, add_zero]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true, MvPolynomial.constantCoeff_smul, map_one, smul_eq_mul, mul_one]
    dsimp [Bosonize.A08.oscWeight]
    ring
  · have hne : (Bosonize.A06.Orientation.right, i) ≠ (Bosonize.A06.Orientation.right, j) := by
      intro h; cases h; exact hij rfl
    simp [hne, hij]

theorem omegaP_cross_creator_annihilator (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.creatorGen M .right i * Bosonize.A08.annihilatorGen M .left j) = 0 := by
  open Bosonize.A08 in
  have hrep_ann_left :
      oscRep M (bogoliubovMap M hp.c (-hp.s) (annihilatorGen M .left j)) =
        (hp.c : ℂ) • oscAnnihilation M (.left, j) +
        (-hp.s : ℂ) • oscCreation M (.right, j) := by
    dsimp [bogoliubovMap, oscRep, annihilatorGen]
    rw [FreeAlgebra.lift_ι_apply, ← Complex.coe_smul hp.c, ← Complex.coe_smul (-hp.s)]
    simp only [map_add, map_smul, FreeAlgebra.lift_ι_apply, Bool.not_false]
    push_cast
    rfl
  open Bosonize.A08 in
  have hrep_cre_right :
      oscRep M (bogoliubovMap M hp.c (-hp.s) (creatorGen M .right i)) =
        (hp.c : ℂ) • oscCreation M (.right, i) +
        (-hp.s : ℂ) • oscAnnihilation M (.left, i) := by
    dsimp [bogoliubovMap, oscRep, creatorGen]
    rw [FreeAlgebra.lift_ι_apply, ← Complex.coe_smul hp.c, ← Complex.coe_smul (-hp.s)]
    simp only [map_add, map_smul, FreeAlgebra.lift_ι_apply, Bool.not_true]
    push_cast
    rfl
  open Bosonize.A08 in
  have ann_X (p q : OscMode M) :
      oscAnnihilation M p (MvPolynomial.X q) = if p = q then (oscWeight p : ℂ) • (1 : OscPoly M) else 0 := by
    dsimp [oscAnnihilation]
    by_cases h : p = q
    · subst h
      simp [MvPolynomial.pderiv_X]
    · simp [MvPolynomial.pderiv_X_of_ne (Ne.symm h), h]
  have ccoeff_zero (p : Bosonize.A08.OscPoly M) : (MvPolynomial.lcoeff ℂ 0) p = MvPolynomial.constantCoeff p := rfl
  open Bosonize.A08 in
  have ccoeff_cre (p : OscMode M) (y : OscPoly M) :
      MvPolynomial.constantCoeff (oscCreation M p y) = 0 := by
    dsimp [oscCreation]
    rw [map_mul, MvPolynomial.constantCoeff_X, zero_mul]
  dsimp [Bosonize.A08.omegaP, Bosonize.A08.omega0]
  rw [ccoeff_zero, map_mul, map_mul]
  simp only [LinearMap.applyₗ_apply_apply, Module.End.mul_apply]
  rw [hrep_ann_left]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Bosonize.A08.oscAnnihilation_one, smul_zero, zero_add]
  have hcre_one : Bosonize.A08.oscCreation M (.right, j) 1 = MvPolynomial.X (.right, j) := by
    simp [Bosonize.A08.oscCreation]
  rw [hcre_one, hrep_cre_right]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [map_add, MvPolynomial.constantCoeff_smul, ccoeff_cre, smul_zero, zero_add,
    MvPolynomial.constantCoeff_smul, map_smul, MvPolynomial.constantCoeff_smul, ann_X]
  have hne : (Bosonize.A06.Orientation.left, i) ≠ (Bosonize.A06.Orientation.right, j) := by
    intro h; cases h
  simp [hne]

theorem ordered_density_kernel (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x y : ZMod (2 * h)) :
    orderedDensityCorrelation h M ζ hp x y =
      densityKernel h M ζ (hp.c ^ 2) (hp.s ^ 2) ((x.val : ℤ) - (y.val : ℤ)) := by
  have sum_fin_icc (f : ℕ → ℂ) :
      (∑ i : Fin M, f (i.val + 1)) = ∑ m ∈ Finset.Icc 1 M, f m := by
    refine Finset.sum_bij (fun i _ => i.val + 1) ?_ ?_ ?_ ?_
    · intro i _
      rw [Finset.mem_Icc]
      exact ⟨Nat.succ_le_succ (Nat.zero_le _), i.isLt⟩
    · intro a _ b _ h
      ext
      exact Nat.succ.inj h
    · intro b hb
      rw [Finset.mem_Icc] at hb
      have hlt : b - 1 < M := by omega
      refine ⟨⟨b - 1, hlt⟩, Finset.mem_univ _, ?_⟩
      dsimp
      omega
    · intro a _
      rfl
  have char_mul_s (m : ℤ) :
      Bosonize.A06.latticeCharacter h ζ (-m) x * Bosonize.A06.latticeCharacter h ζ m y =
        Bosonize.A01.integerCharacter ζ (-m) ((x.val : ℤ) - (y.val : ℤ)) := by
    dsimp [Bosonize.A06.latticeCharacter, Bosonize.A01.integerCharacter]
    rw [← zpow_add₀ hζ]
    congr 1
    ring
  have char_mul_c (m : ℤ) :
      Bosonize.A06.latticeCharacter h ζ m x * Bosonize.A06.latticeCharacter h ζ (-m) y =
        Bosonize.A01.integerCharacter ζ m ((x.val : ℤ) - (y.val : ℤ)) := by
    dsimp [Bosonize.A06.latticeCharacter, Bosonize.A01.integerCharacter]
    rw [← zpow_add₀ hζ]
    congr 1
    ring
  have term_eval (i j : Fin M) :
      Bosonize.A08.omegaP M hp (
        (Bosonize.A06.latticeCharacter h ζ (-((i.val + 1 : ℕ) : ℤ)) x • Bosonize.A08.creatorGen M .right i +
         Bosonize.A06.latticeCharacter h ζ ((i.val + 1 : ℕ) : ℤ) x • Bosonize.A08.annihilatorGen M .right i) *
        (Bosonize.A06.latticeCharacter h ζ (-((j.val + 1 : ℕ) : ℤ)) y • Bosonize.A08.creatorGen M .right j +
         Bosonize.A06.latticeCharacter h ζ ((j.val + 1 : ℕ) : ℤ) y • Bosonize.A08.annihilatorGen M .right j)) =
        if i = j then ((i.val + 1 : ℕ) : ℂ) *
          ((hp.s : ℂ) ^ 2 * (Bosonize.A06.latticeCharacter h ζ (-((i.val + 1 : ℕ) : ℤ)) x *
                             Bosonize.A06.latticeCharacter h ζ ((j.val + 1 : ℕ) : ℤ) y) +
           (hp.c : ℂ) ^ 2 * (Bosonize.A06.latticeCharacter h ζ ((i.val + 1 : ℕ) : ℤ) x *
                             Bosonize.A06.latticeCharacter h ζ (-((j.val + 1 : ℕ) : ℤ)) y)) else 0 := by
    have h1 :
      (Bosonize.A06.latticeCharacter h ζ (-((i.val + 1 : ℕ) : ℤ)) x • Bosonize.A08.creatorGen M .right i +
       Bosonize.A06.latticeCharacter h ζ ((i.val + 1 : ℕ) : ℤ) x • Bosonize.A08.annihilatorGen M .right i) *
      (Bosonize.A06.latticeCharacter h ζ (-((j.val + 1 : ℕ) : ℤ)) y • Bosonize.A08.creatorGen M .right j +
       Bosonize.A06.latticeCharacter h ζ ((j.val + 1 : ℕ) : ℤ) y • Bosonize.A08.annihilatorGen M .right j) =
        (Bosonize.A06.latticeCharacter h ζ (-((i.val + 1 : ℕ) : ℤ)) x *
         Bosonize.A06.latticeCharacter h ζ (-((j.val + 1 : ℕ) : ℤ)) y) •
          (Bosonize.A08.creatorGen M .right i * Bosonize.A08.creatorGen M .right j) +
        (Bosonize.A06.latticeCharacter h ζ (-((i.val + 1 : ℕ) : ℤ)) x *
         Bosonize.A06.latticeCharacter h ζ ((j.val + 1 : ℕ) : ℤ) y) •
          (Bosonize.A08.creatorGen M .right i * Bosonize.A08.annihilatorGen M .right j) +
        (Bosonize.A06.latticeCharacter h ζ ((i.val + 1 : ℕ) : ℤ) x *
         Bosonize.A06.latticeCharacter h ζ (-((j.val + 1 : ℕ) : ℤ)) y) •
          (Bosonize.A08.annihilatorGen M .right i * Bosonize.A08.creatorGen M .right j) +
        (Bosonize.A06.latticeCharacter h ζ ((i.val + 1 : ℕ) : ℤ) x *
         Bosonize.A06.latticeCharacter h ζ ((j.val + 1 : ℕ) : ℤ) y) •
          (Bosonize.A08.annihilatorGen M .right i * Bosonize.A08.annihilatorGen M .right j) := by
      simp only [add_mul, mul_add, smul_mul_smul]
      abel
    rw [h1]
    simp only [map_add, map_smul, smul_eq_mul,
      omegaP_creator_creator_right, omegaP_annihilator_annihilator_right,
      omegaP_creator_annihilator_right, omegaP_annihilator_creator_right,
      mul_zero, add_zero, zero_add]
    by_cases hij : i = j
    · subst hij
      simp only [ite_true]
      ring
    · simp [hij]
  dsimp [orderedDensityCorrelation, oscDensityR, densityKernel]
  rw [smul_mul_smul, map_smul, smul_eq_mul]
  have hsq : ((2 * h : ℕ) : ℂ)⁻¹ * ((2 * h : ℕ) : ℂ)⁻¹ = (((2 * h : ℕ) : ℂ)⁻¹) ^ 2 := by ring
  rw [hsq]
  congr 1
  rw [Finset.sum_mul, map_sum]
  have hinner (i : Fin M) :
      (Bosonize.A08.omegaP M hp)
        ((Bosonize.A06.latticeCharacter h ζ (-((i.val + 1 : ℕ) : ℤ)) x • Bosonize.A08.creatorGen M .right i +
          Bosonize.A06.latticeCharacter h ζ ((i.val + 1 : ℕ) : ℤ) x • Bosonize.A08.annihilatorGen M .right i) *
          ∑ j : Fin M,
            (Bosonize.A06.latticeCharacter h ζ (-((j.val + 1 : ℕ) : ℤ)) y • Bosonize.A08.creatorGen M .right j +
             Bosonize.A06.latticeCharacter h ζ ((j.val + 1 : ℕ) : ℤ) y • Bosonize.A08.annihilatorGen M .right j)) =
      ((i.val + 1 : ℕ) : ℂ) *
        ((hp.s : ℂ) ^ 2 * Bosonize.A01.integerCharacter ζ (-((i.val + 1 : ℕ) : ℤ)) ((x.val : ℤ) - (y.val : ℤ)) +
         (hp.c : ℂ) ^ 2 * Bosonize.A01.integerCharacter ζ ((i.val + 1 : ℕ) : ℤ) ((x.val : ℤ) - (y.val : ℤ))) := by
    rw [Finset.mul_sum, map_sum]
    simp_rw [term_eval]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [char_mul_s, char_mul_c]
  trans ∑ i : Fin M,
      ((i.val + 1 : ℕ) : ℂ) *
        ((hp.s : ℂ) ^ 2 * Bosonize.A01.integerCharacter ζ (-((i.val + 1 : ℕ) : ℤ)) ((x.val : ℤ) - (y.val : ℤ)) +
         (hp.c : ℂ) ^ 2 * Bosonize.A01.integerCharacter ζ ((i.val + 1 : ℕ) : ℤ) ((x.val : ℤ) - (y.val : ℤ)))
  · apply Finset.sum_congr rfl
    intro i _
    exact hinner i
  · let f (m : ℕ) : ℂ :=
      (m : ℂ) *
        ((hp.s : ℂ) ^ 2 * Bosonize.A01.integerCharacter ζ (-(m : ℤ)) ((x.val : ℤ) - (y.val : ℤ)) +
         (hp.c : ℂ) ^ 2 * Bosonize.A01.integerCharacter ζ (m : ℤ) ((x.val : ℤ) - (y.val : ℤ)))
    have hf : (∑ i : Fin M,
      ((i.val + 1 : ℕ) : ℂ) *
        ((hp.s : ℂ) ^ 2 * Bosonize.A01.integerCharacter ζ (-((i.val + 1 : ℕ) : ℤ)) ((x.val : ℤ) - (y.val : ℤ)) +
         (hp.c : ℂ) ^ 2 * Bosonize.A01.integerCharacter ζ ((i.val + 1 : ℕ) : ℤ) ((x.val : ℤ) - (y.val : ℤ)))) =
      ∑ i : Fin M, f (i.val + 1) := rfl
    rw [hf, sum_fin_icc f]
    apply Finset.sum_congr rfl
    intro m _
    dsimp [f]
    push_cast
    ring

theorem ordered_density_kernel_lattice (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (hp : Bosonize.Ch18.HyperbolicPair) (x y : ZMod (2 * h)) :
    orderedDensityCorrelation h M ζ hp x y =
      (((2 * h : ℕ) : ℂ)⁻¹) ^ 2 * ∑ m ∈ Finset.Icc 1 M, (m : ℂ) *
        ((hp.s : ℂ) ^ 2 * Bosonize.A06.latticeCharacter h ζ (-(m : ℤ)) (x - y) +
         (hp.c : ℂ) ^ 2 * Bosonize.A06.latticeCharacter h ζ (m : ℤ) (x - y)) := by
  have hroot : ζ ≠ 0 := Bosonize.A01.root_ne_zero (2 * h) ζ hζ
  have hc (z : ZMod (2 * h)) : ((z.val : ℤ) : ZMod (2 * h)) = z := by simp
  have hbridge (k : ℤ) (z : ZMod (2 * h)) :
      Bosonize.A06.latticeCharacter h ζ k z = Bosonize.A01.residueCharacter (2 * h) ζ (k : ZMod (2 * h)) z := by
    simpa only [hc, Bosonize.A06.latticeCharacter] using
      (Bosonize.A01.residue_character_int_cast (2 * h) ζ hζ k (z.val : ℤ)).symm
  have hd (k : ℤ) :
      Bosonize.A06.latticeCharacter h ζ k (x - y) =
        Bosonize.A01.integerCharacter ζ k ((x.val : ℤ) - (y.val : ℤ)) := by
    rw [hbridge]
    simpa only [Int.cast_sub, hc] using
      Bosonize.A01.residue_character_int_cast (2 * h) ζ hζ k ((x.val : ℤ) - (y.val : ℤ))
  rw [ordered_density_kernel h M ζ hroot hp x y]
  dsimp [densityKernel]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [← hd (- (m : ℤ)), ← hd (m : ℤ)]
  push_cast
  ring

theorem density_commutator_expectation (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x y : ZMod (2 * h)) :
    orderedDensityCorrelation h M ζ hp x y - orderedDensityCorrelation h M ζ hp y x =
      densityKernel h M ζ 1 (-1) ((x.val : ℤ) - (y.val : ℤ)) := by
  rw [ordered_density_kernel h M ζ hζ hp x y, ordered_density_kernel h M ζ hζ hp y x]
  dsimp [densityKernel]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  have hneg1 : Bosonize.A01.integerCharacter ζ (-(m : ℤ)) ((y.val : ℤ) - (x.val : ℤ)) =
      Bosonize.A01.integerCharacter ζ (m : ℤ) ((x.val : ℤ) - (y.val : ℤ)) := by
    dsimp [Bosonize.A01.integerCharacter]
    congr 1
    ring
  have hneg2 : Bosonize.A01.integerCharacter ζ (m : ℤ) ((y.val : ℤ) - (x.val : ℤ)) =
      Bosonize.A01.integerCharacter ζ (-(m : ℤ)) ((x.val : ℤ) - (y.val : ℤ)) := by
    dsimp [Bosonize.A01.integerCharacter]
    congr 1
    ring
  rw [hneg1, hneg2]
  have hcs : (hp.c : ℂ) ^ 2 - (hp.s : ℂ) ^ 2 = 1 := by exact_mod_cast hp.hyperbolic_id
  push_cast
  linear_combination (m : ℂ) * (Bosonize.A01.integerCharacter ζ (m : ℤ) ((x.val : ℤ) - (y.val : ℤ)) -
    Bosonize.A01.integerCharacter ζ (-(m : ℤ)) ((x.val : ℤ) - (y.val : ℤ))) * hcs

theorem symmetrized_density_kernel (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x y : ZMod (2 * h)) :
    (orderedDensityCorrelation h M ζ hp x y + orderedDensityCorrelation h M ζ hp y x) / 2 =
      densityKernel h M ζ
        ((Bosonize.Ch18.luttingerG hp + (Bosonize.Ch18.luttingerG hp)⁻¹) / 4)
        ((Bosonize.Ch18.luttingerG hp + (Bosonize.Ch18.luttingerG hp)⁻¹) / 4)
        ((x.val : ℤ) - (y.val : ℤ)) := by
  rw [ordered_density_kernel h M ζ hζ hp x y, ordered_density_kernel h M ζ hζ hp y x]
  dsimp [densityKernel]
  rw [← mul_add, mul_div_assoc, ← Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  have hneg1 : Bosonize.A01.integerCharacter ζ (-(m : ℤ)) ((y.val : ℤ) - (x.val : ℤ)) =
      Bosonize.A01.integerCharacter ζ (m : ℤ) ((x.val : ℤ) - (y.val : ℤ)) := by
    dsimp [Bosonize.A01.integerCharacter]
    congr 1
    ring
  have hneg2 : Bosonize.A01.integerCharacter ζ (m : ℤ) ((y.val : ℤ) - (x.val : ℤ)) =
      Bosonize.A01.integerCharacter ζ (-(m : ℤ)) ((x.val : ℤ) - (y.val : ℤ)) := by
    dsimp [Bosonize.A01.integerCharacter]
    congr 1
    ring
  rw [hneg1, hneg2]
  have hlut : ((hp.c : ℂ) ^ 2 + (hp.s : ℂ) ^ 2) / 2 =
      (((Bosonize.Ch18.luttingerG hp + (Bosonize.Ch18.luttingerG hp)⁻¹) / 4 : ℝ) : ℂ) := by
    have h := congr_arg (fun r : ℝ => (r : ℂ)) (Bosonize.Ch18.hyperbolic_coeff_eq_luttinger hp)
    push_cast at h ⊢
    linear_combination (1 / 2 : ℂ) * h
  push_cast at hlut ⊢
  linear_combination (m : ℂ) *
    (Bosonize.A01.integerCharacter ζ (-(m : ℤ)) ((x.val : ℤ) - (y.val : ℤ)) +
     Bosonize.A01.integerCharacter ζ (m : ℤ) ((x.val : ℤ) - (y.val : ℤ))) * hlut

theorem s_sq_eq_luttinger (hp : Bosonize.Ch18.HyperbolicPair) :
    hp.s ^ 2 = (Bosonize.Ch18.luttingerG hp + (Bosonize.Ch18.luttingerG hp)⁻¹ - 2) / 4 := by
  have h1 := Bosonize.Ch18.hyperbolic_coeff_eq_luttinger hp
  have h2 := hp.hyperbolic_id
  linear_combination (1 / 2 : ℝ) * h1 - (1 / 2 : ℝ) * h2

theorem c_sq_eq_luttinger (hp : Bosonize.Ch18.HyperbolicPair) :
    hp.c ^ 2 = (Bosonize.Ch18.luttingerG hp + (Bosonize.Ch18.luttingerG hp)⁻¹ + 2) / 4 := by
  have h1 := Bosonize.Ch18.hyperbolic_coeff_eq_luttinger hp
  have h2 := hp.hyperbolic_id
  linear_combination (1 / 2 : ℝ) * h1 + (1 / 2 : ℝ) * h2

theorem density_kernel_diagonal (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x : ZMod (2 * h)) :
    orderedDensityCorrelation h M ζ hp x x =
      ((((hp.c ^ 2 + hp.s ^ 2) * ((M * (M + 1) : ℝ) / 2) / ((2 * h : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)) := by
  have sum_icc_id :
      (∑ m ∈ Finset.Icc 1 M, (m : ℂ)) = (((M * (M + 1) : ℝ) / 2 : ℝ) : ℂ) := by
    induction M with
    | zero =>
      have : Finset.Icc 1 0 = ∅ := Finset.Icc_eq_empty (by omega)
      rw [this, Finset.sum_empty]
      push_cast
      ring
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih]
      push_cast
      ring
  rw [ordered_density_kernel h M ζ hζ hp x x]
  dsimp [densityKernel]
  have hsub : (x.val : ℤ) - (x.val : ℤ) = 0 := sub_self _
  rw [hsub]
  have hchar (k : ℤ) : Bosonize.A01.integerCharacter ζ k 0 = 1 := by
    simp [Bosonize.A01.integerCharacter]
  have hsum :
      (∑ m ∈ Finset.Icc 1 M, (m : ℂ) *
        (((hp.s ^ 2 : ℝ) : ℂ) * Bosonize.A01.integerCharacter ζ (-(m : ℤ)) 0 +
         ((hp.c ^ 2 : ℝ) : ℂ) * Bosonize.A01.integerCharacter ζ (m : ℤ) 0)) =
      ((hp.c ^ 2 + hp.s ^ 2 : ℝ) : ℂ) * (((M * (M + 1) : ℝ) / 2 : ℝ) : ℂ) := by
    have hterm :
        (∑ m ∈ Finset.Icc 1 M, (m : ℂ) *
          (((hp.s ^ 2 : ℝ) : ℂ) * Bosonize.A01.integerCharacter ζ (-(m : ℤ)) 0 +
           ((hp.c ^ 2 : ℝ) : ℂ) * Bosonize.A01.integerCharacter ζ (m : ℤ) 0)) =
        (∑ m ∈ Finset.Icc 1 M, ((hp.c ^ 2 + hp.s ^ 2 : ℝ) : ℂ) * (m : ℂ)) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [hchar, hchar]
      push_cast
      ring
    rw [hterm, ← Finset.mul_sum, sum_icc_id]
  rw [hsum]
  push_cast
  ring

theorem density_kernel_diagonal_pos (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x : ZMod (2 * h))
    (hh : 0 < h) (hM : 1 ≤ M) :
    0 < (orderedDensityCorrelation h M ζ hp x x).re := by
  rw [density_kernel_diagonal h M ζ hζ hp x]
  simp only [Complex.ofReal_re]
  have hcs_pos : 0 < hp.c ^ 2 + hp.s ^ 2 := by
    have hs2 : 0 ≤ hp.s ^ 2 := sq_nonneg hp.s
    have hid := hp.hyperbolic_id
    linarith
  have hM_pos : 0 < (M * (M + 1) : ℝ) / 2 := by
    have h1 : 0 < (M : ℝ) := by positivity
    have h2 : 0 < (M + 1 : ℝ) := by positivity
    positivity
  have hden_pos : 0 < ((2 * h : ℕ) : ℝ) ^ 2 := by
    have h2h : 0 < ((2 * h : ℕ) : ℝ) := by positivity
    positivity
  exact div_pos (mul_pos hcs_pos hM_pos) hden_pos

theorem ordered_density_free (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (hs : hp.s = 0) (x y : ZMod (2 * h)) :
    orderedDensityCorrelation h M ζ hp x y =
      densityKernel h M ζ 1 0 ((x.val : ℤ) - (y.val : ℤ)) := by
  rw [ordered_density_kernel h M ζ hζ hp x y]
  have hs2 : hp.s ^ 2 = 0 := by rw [hs, sq, mul_zero]
  have hc2 : hp.c ^ 2 = 1 := by
    have hid := hp.hyperbolic_id
    linarith
  rw [hc2, hs2]

section Fock

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable def fockDensityR (h M : ℕ) (ζ : ℂ) (branches : Bosonize.A06.Branches σ) (x : ZMod (2 * h)) :
    Bosonize.A05.Operators σ h :=
  (((2 * h : ℕ) : ℂ)⁻¹) • ∑ m ∈ Finset.Icc 1 M,
    (Bosonize.A06.latticeCharacter h ζ (-(m : ℤ)) x • Bosonize.A05.rho h branches.rightSpecies (m : ℤ) +
     Bosonize.A06.latticeCharacter h ζ (m : ℤ) x • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)))

theorem ground_lowering_raising (h M : ℕ) (hh : 0 < h) (m n : ℕ)
    (hm : 1 ≤ m) (hmM : m ≤ M) (hnM : n ≤ M)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M 0 Ns branches.rightSpecies) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) *
         Bosonize.A05.rho h branches.rightSpecies (n : ℤ)) =
      if m = n then (m : ℂ) else 0 := by
  have hg := Bosonize.A05.ground_mem_budget h hh Ns hN 0
  have hl := Bosonize.A05.rho_lowering_budget_zero h hh branches.rightSpecies m 0 (by omega) Ns (Bosonize.A05.groundKet h Ns) hg
  have hmarg : |-(m : ℤ)| + |(n : ℤ)| + (0 : ℤ) + |Ns branches.rightSpecies| ≤ (h : ℤ) := by
    unfold Bosonize.A06.marginAt at hmargin
    simp only [abs_neg, abs_of_nonneg (Int.natCast_nonneg m), abs_of_nonneg (Int.natCast_nonneg n)]
    omega
  have hc := Bosonize.A06.joint_signed_current_commutator h 0 hh Ns branches.rightSpecies (-(m : ℤ)) (n : ℤ) hmarg (Bosonize.A05.groundKet h Ns) hg
  simp only [Bosonize.A02.commutator, LinearMap.sub_apply, Module.End.mul_apply] at hc
  rw [hl, map_zero, sub_zero] at hc
  dsimp [Bosonize.A08.vectorState]
  rw [hc, inner_smul_right]
  have hnorm : inner ℂ (Bosonize.A05.groundKet h Ns) (Bosonize.A05.groundKet h Ns) = 1 := by
    have h1 := Bosonize.A08.vectorState_ground_one h Ns
    simpa [Bosonize.A08.vectorState] using h1
  rw [hnorm, mul_one]
  by_cases hmn : m = n
  · subst hmn
    have hzero : -(m : ℤ) + (m : ℤ) = 0 := by omega
    simp [Bosonize.Ch10.schwingerCoefficient, hzero]
  · have hnonzero : -(m : ℤ) + (n : ℤ) ≠ 0 := by omega
    simp [Bosonize.Ch10.schwingerCoefficient, hmn, hnonzero]

theorem ground_raising_lowering (h : ℕ) (hh : 0 < h) (m n : ℕ) (hn : 1 ≤ n)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.rho h branches.rightSpecies (m : ℤ) *
         Bosonize.A05.rho h branches.rightSpecies (-(n : ℤ))) = 0 := by
  have hg := Bosonize.A05.ground_mem_budget h hh Ns hN 0
  have hl := Bosonize.A05.rho_lowering_budget_zero h hh branches.rightSpecies n 0 (by omega) Ns (Bosonize.A05.groundKet h Ns) hg
  dsimp [Bosonize.A08.vectorState]
  rw [hl, map_zero, inner_zero_right]

theorem ground_raising_raising (h : ℕ) (hh : 0 < h) (m n : ℕ) (hm : 1 ≤ m)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.rho h branches.rightSpecies (m : ℤ) *
         Bosonize.A05.rho h branches.rightSpecies (n : ℤ)) = 0 := by
  have hg := Bosonize.A05.ground_mem_budget h hh Ns hN 0
  have hl := Bosonize.A05.rho_lowering_budget_zero h hh branches.rightSpecies m 0 (by omega) Ns (Bosonize.A05.groundKet h Ns) hg
  dsimp [Bosonize.A08.vectorState]
  rw [← LinearMap.adjoint_inner_left (Bosonize.A05.rho h branches.rightSpecies (m : ℤ))]
  rw [Bosonize.A05.rho_adjoint, hl, inner_zero_left]

theorem ground_lowering_lowering (h : ℕ) (hh : 0 < h) (m n : ℕ) (hn : 1 ≤ n)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) *
         Bosonize.A05.rho h branches.rightSpecies (-(n : ℤ))) = 0 := by
  have hg := Bosonize.A05.ground_mem_budget h hh Ns hN 0
  have hl := Bosonize.A05.rho_lowering_budget_zero h hh branches.rightSpecies n 0 (by omega) Ns (Bosonize.A05.groundKet h Ns) hg
  dsimp [Bosonize.A08.vectorState]
  rw [hl, map_zero, inner_zero_right]

theorem excited_ket_norm_sq (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hmM : m ≤ M)
    (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M 0 Ns (Bosonize.A06.speciesOf branches η)) :
    ‖Bosonize.Ch16.excitedKet h Ns branches η m‖ ^ 2 = (m : ℝ) := by
  set ν := Bosonize.A06.speciesOf branches η
  set g := Bosonize.A05.groundKet h Ns
  set X := Bosonize.A05.rho h ν (m : ℤ)
  have hg := Bosonize.A05.ground_mem_budget h hh Ns hN 0
  have hl := Bosonize.A05.rho_lowering_budget_zero h hh ν m 0 (by omega) Ns g hg
  have hmarg : |-(m : ℤ)| + |(m : ℤ)| + (0 : ℤ) + |Ns ν| ≤ (h : ℤ) := by
    unfold Bosonize.A06.marginAt at hmargin
    simp only [abs_neg, abs_of_nonneg (Int.natCast_nonneg m)]
    omega
  have hc := Bosonize.A06.joint_signed_current_commutator h 0 hh Ns ν (-(m : ℤ)) (m : ℤ) hmarg g hg
  simp only [Bosonize.A02.commutator, LinearMap.sub_apply, Module.End.mul_apply] at hc
  rw [hl, map_zero, sub_zero] at hc
  have hsch : Bosonize.Ch10.schwingerCoefficient (-(m : ℤ)) (m : ℤ) = (m : ℂ) := by
    unfold Bosonize.Ch10.schwingerCoefficient
    have hzero : -(m : ℤ) + (m : ℤ) = 0 := by omega
    simp [hzero]
  rw [hsch] at hc
  have hadj : LinearMap.adjoint (Bosonize.A05.rho h ν (-(m : ℤ))) = X := by
    simp [X, Bosonize.A05.rho_adjoint]
  have hinner := LinearMap.adjoint_inner_left (Bosonize.A05.rho h ν (-(m : ℤ))) (X g) g
  rw [hadj] at hinner
  have hg_norm : inner ℂ g g = 1 := by
    have h1 := Bosonize.A08.vectorState_ground_one h Ns
    simpa [Bosonize.A08.vectorState] using h1
  have hinner_eq : inner ℂ (X g) (X g) = (m : ℂ) := by
    rw [hinner, hc, inner_smul_right, hg_norm, mul_one]
  have hnorm_sq : inner ℂ (X g) (X g) = ((‖X g‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    push_cast
    rfl
  rw [hnorm_sq] at hinner_eq
  exact_mod_cast hinner_eq

theorem ground_dressed_number (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hp : Bosonize.Ch18.HyperbolicPair)
    (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.branchMargins h M 0 Ns branches) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches η *
         Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches η) =
      (m : ℂ) * (hp.s : ℂ) ^ 2 := by
  set g := Bosonize.A05.groundKet h Ns
  set C := Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches η
  set A := Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches η
  set v := Bosonize.Ch16.excitedKet h Ns branches (Bosonize.A07Interactions.oppositeOrientation η) m
  have hg := Bosonize.A05.ground_mem_budget h hh Ns hN 0
  have hl : Bosonize.A05.rho h (Bosonize.A06.speciesOf branches η) (-(m : ℤ)) g = 0 :=
    Bosonize.A05.rho_lowering_budget_zero h hh (Bosonize.A06.speciesOf branches η) m 0 (by omega) Ns g hg
  have hAg : A g = (hp.s : ℂ) • v := by
    dsimp [A, Bosonize.A07Interactions.bogoliubovAnnihilator, v, Bosonize.Ch16.excitedKet]
    rw [hl, smul_zero, zero_add]
  have hadj := Bosonize.A07Interactions.bogoliubov_creator_adjoint h m hp.c hp.s branches η
  have hinner := LinearMap.adjoint_inner_left C (A g) g
  rw [hadj] at hinner
  dsimp [Bosonize.A08.vectorState]
  rw [← hinner, hAg, inner_smul_left, inner_smul_right]
  have hmar : Bosonize.A06.marginAt h M 0 Ns (Bosonize.A06.speciesOf branches (Bosonize.A07Interactions.oppositeOrientation η)) := by
    cases η
    · exact hmargin.2
    · exact hmargin.1
  have hnorm := excited_ket_norm_sq h M m hh hm hmM branches (Bosonize.A07Interactions.oppositeOrientation η) Ns hN hmar
  have hinner_v : inner ℂ v v = (m : ℂ) := by
    have h1 : inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
      push_cast
      rfl
    change ‖v‖ ^ 2 = (m : ℝ) at hnorm
    rw [h1, hnorm]
    push_cast
    rfl
  rw [hinner_v]
  have hs_conj : starRingEnd ℂ (hp.s : ℂ) = (hp.s : ℂ) := Complex.conj_ofReal hp.s
  rw [hs_conj]
  ring

theorem ground_dressed_reverse (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hp : Bosonize.Ch18.HyperbolicPair)
    (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.branchMargins h M 0 Ns branches) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches η *
         Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches η) =
      (m : ℂ) * (hp.c : ℂ) ^ 2 := by
  set g := Bosonize.A05.groundKet h Ns
  set C := Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches η
  set A := Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches η
  set v := Bosonize.Ch16.excitedKet h Ns branches η m
  have hg := Bosonize.A05.ground_mem_budget h hh Ns hN 0
  have hl : Bosonize.A05.rho h (Bosonize.A06.speciesOf branches (Bosonize.A07Interactions.oppositeOrientation η)) (-(m : ℤ)) g = 0 :=
    Bosonize.A05.rho_lowering_budget_zero h hh (Bosonize.A06.speciesOf branches (Bosonize.A07Interactions.oppositeOrientation η)) m 0 (by omega) Ns g hg
  have hCg : C g = (hp.c : ℂ) • v := by
    dsimp [C, Bosonize.A07Interactions.bogoliubovCreator, v, Bosonize.Ch16.excitedKet]
    rw [hl, smul_zero, add_zero]
  have hadj : LinearMap.adjoint A = C := by
    have hc := Bosonize.A07Interactions.bogoliubov_creator_adjoint h m hp.c hp.s branches η
    change LinearMap.adjoint C = A at hc
    rw [← hc, LinearMap.adjoint_adjoint]
  have hinner := LinearMap.adjoint_inner_left A (C g) g
  rw [hadj] at hinner
  dsimp [Bosonize.A08.vectorState]
  rw [← hinner, hCg, inner_smul_left, inner_smul_right]
  have hmar : Bosonize.A06.marginAt h M 0 Ns (Bosonize.A06.speciesOf branches η) := by
    cases η
    · exact hmargin.1
    · exact hmargin.2
  have hnorm := excited_ket_norm_sq h M m hh hm hmM branches η Ns hN hmar
  have hinner_v : inner ℂ v v = (m : ℂ) := by
    have h1 : inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
      push_cast
      rfl
    change ‖v‖ ^ 2 = (m : ℝ) at hnorm
    rw [h1, hnorm]
    push_cast
    rfl
  rw [hinner_v]
  have hc_conj : starRingEnd ℂ (hp.c : ℂ) = (hp.c : ℂ) := Complex.conj_ofReal hp.c
  rw [hc_conj]
  ring

theorem ground_not_dressed_vacuum (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hp : Bosonize.Ch18.HyperbolicPair) (hs : hp.s ≠ 0)
    (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.branchMargins h M 0 Ns branches) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches η *
         Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches η) ≠ 0 := by
  rw [ground_dressed_number h M m hh hm hmM hp branches η Ns hN hmargin]
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hs0 : (hp.s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hs2 : (hp.s : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hs0
  exact mul_ne_zero hm0 hs2

theorem fock_ground_density_kernel (h M : ℕ) [NeZero (2 * h)] (hh : 0 < h)
    (ζ : ℂ) (hζ : ζ ≠ 0) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M 0 Ns branches.rightSpecies)
    (x y : ZMod (2 * h)) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (fockDensityR h M ζ branches x * fockDensityR h M ζ branches y) =
      densityKernel h M ζ 1 0 ((x.val : ℤ) - (y.val : ℤ)) := by
  set g := Bosonize.A05.groundKet h Ns
  let vs : Bosonize.A05.Operators σ h →ₗ[ℂ] ℂ :=
    { toFun := fun X => Bosonize.A08.vectorState h g X
      map_add' := fun X Y => by dsimp [Bosonize.A08.vectorState]; rw [inner_add_right]
      map_smul' := fun c X => by dsimp [Bosonize.A08.vectorState]; rw [inner_smul_right] }
  have hchar (m : ℕ) :
      Bosonize.A06.latticeCharacter h ζ (m : ℤ) x *
      Bosonize.A06.latticeCharacter h ζ (-(m : ℤ)) y =
      Bosonize.A01.integerCharacter ζ (m : ℤ) ((x.val : ℤ) - (y.val : ℤ)) := by
    dsimp [Bosonize.A06.latticeCharacter, Bosonize.A01.integerCharacter]
    rw [← zpow_add₀ hζ]
    congr 1
    ring
  let term (z : ZMod (2 * h)) (m : ℕ) : Bosonize.A05.Operators σ h :=
    Bosonize.A06.latticeCharacter h ζ (-(m : ℤ)) z • Bosonize.A05.rho h branches.rightSpecies (m : ℤ) +
    Bosonize.A06.latticeCharacter h ζ (m : ℤ) z • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ))
  have hterm (m n : ℕ) (hm : m ∈ Finset.Icc 1 M) (hn : n ∈ Finset.Icc 1 M) :
      vs (term x m * term y n) =
        if m = n then (m : ℂ) * Bosonize.A01.integerCharacter ζ (m : ℤ) ((x.val : ℤ) - (y.val : ℤ)) else 0 := by
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmM : m ≤ M := (Finset.mem_Icc.mp hm).2
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnM : n ≤ M := (Finset.mem_Icc.mp hn).2
    have hexp : term x m * term y n =
        (Bosonize.A06.latticeCharacter h ζ (-(m : ℤ)) x * Bosonize.A06.latticeCharacter h ζ (-(n : ℤ)) y) •
          (Bosonize.A05.rho h branches.rightSpecies (m : ℤ) * Bosonize.A05.rho h branches.rightSpecies (n : ℤ)) +
        (Bosonize.A06.latticeCharacter h ζ (-(m : ℤ)) x * Bosonize.A06.latticeCharacter h ζ (n : ℤ) y) •
          (Bosonize.A05.rho h branches.rightSpecies (m : ℤ) * Bosonize.A05.rho h branches.rightSpecies (-(n : ℤ))) +
        (Bosonize.A06.latticeCharacter h ζ (m : ℤ) x * Bosonize.A06.latticeCharacter h ζ (-(n : ℤ)) y) •
          (Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) * Bosonize.A05.rho h branches.rightSpecies (n : ℤ)) +
        (Bosonize.A06.latticeCharacter h ζ (m : ℤ) x * Bosonize.A06.latticeCharacter h ζ (n : ℤ) y) •
          (Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) * Bosonize.A05.rho h branches.rightSpecies (-(n : ℤ))) := by
      dsimp [term]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
      module
    rw [hexp]
    simp only [map_add, map_smul, smul_eq_mul]
    change _ * Bosonize.A08.vectorState h g _ + _ * Bosonize.A08.vectorState h g _ +
      _ * Bosonize.A08.vectorState h g _ + _ * Bosonize.A08.vectorState h g _ = _
    rw [ground_raising_raising h hh m n hm1 branches Ns hN]
    rw [ground_raising_lowering h hh m n hn1 branches Ns hN]
    rw [ground_lowering_lowering h hh m n hn1 branches Ns hN]
    rw [ground_lowering_raising h M hh m n hm1 hmM hnM branches Ns hN hmargin]
    split_ifs with hmn
    · subst hmn
      rw [hchar]
      ring
    · ring
  have hmul : fockDensityR h M ζ branches x * fockDensityR h M ζ branches y =
      ((((2 * h : ℕ) : ℂ)⁻¹) ^ 2) •
        (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M, (term x m * term y n)) := by
    change ((((2 * h : ℕ) : ℂ)⁻¹) • ∑ m ∈ Finset.Icc 1 M, term x m) *
      ((((2 * h : ℕ) : ℂ)⁻¹) • ∑ n ∈ Finset.Icc 1 M, term y n) = _
    rw [smul_mul_smul, sq]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
  change vs (fockDensityR h M ζ branches x * fockDensityR h M ζ branches y) = _
  rw [hmul, map_smul vs, smul_eq_mul, map_sum vs]
  have hinner_sum (m : ℕ) (hm : m ∈ Finset.Icc 1 M) :
      vs (∑ n ∈ Finset.Icc 1 M, (term x m * term y n)) =
        (m : ℂ) * Bosonize.A01.integerCharacter ζ (m : ℤ) ((x.val : ℤ) - (y.val : ℤ)) := by
    rw [map_sum vs]
    rw [Finset.sum_eq_single m]
    · have hterm_m := hterm m m hm hm
      simp only [ite_true] at hterm_m
      exact hterm_m
    · intro n hn hnm
      have hterm_n := hterm m n hm hn
      have hneq : m ≠ n := Ne.symm hnm
      simp only [hneq, ite_false] at hterm_n
      exact hterm_n
    · intro hm_not
      exact (hm_not hm).elim
  have houter_sum :
      (∑ m ∈ Finset.Icc 1 M, vs (∑ n ∈ Finset.Icc 1 M, (term x m * term y n))) =
        ∑ m ∈ Finset.Icc 1 M, (m : ℂ) * Bosonize.A01.integerCharacter ζ (m : ℤ) ((x.val : ℤ) - (y.val : ℤ)) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact hinner_sum m hm
  rw [houter_sum]
  unfold densityKernel
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  push_cast
  ring

theorem fock_ground_matches_free_state (h M : ℕ) [NeZero (2 * h)] (hh : 0 < h)
    (ζ : ℂ) (hζ : ζ ≠ 0) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M 0 Ns branches.rightSpecies)
    (x y : ZMod (2 * h)) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (fockDensityR h M ζ branches x * fockDensityR h M ζ branches y) =
      orderedDensityCorrelation h M ζ freePair x y := by
  rw [fock_ground_density_kernel h M hh ζ hζ branches Ns hN hmargin x y]
  rw [ordered_density_kernel h M ζ hζ freePair x y]
  simp [freePair]

end Fock

theorem concrete_correlation_witness :
    Bosonize.A08.omegaP 2 Bosonize.Ch18.concretePair
        (Bosonize.A08.creatorGen 2 .right (1 : Fin 2) *
         Bosonize.A08.annihilatorGen 2 .right (1 : Fin 2)) = (9 : ℂ) / 8 ∧
      Bosonize.A08.omegaP 2 Bosonize.Ch18.concretePair
        (Bosonize.A08.annihilatorGen 2 .right (1 : Fin 2) *
         Bosonize.A08.creatorGen 2 .right (1 : Fin 2)) = (25 : ℂ) / 8 ∧
      Bosonize.A08.omegaP 2 Bosonize.Ch18.concretePair
        (Bosonize.A08.creatorGen 2 .right (1 : Fin 2) *
         Bosonize.A08.creatorGen 2 .left (1 : Fin 2)) = -(15 : ℂ) / 8 ∧
      orderedDensityCorrelation 8 2 (Bosonize.A01.canonicalRoot (2 * 8))
        Bosonize.Ch18.concretePair 0 0 = (51 : ℂ) / 2048 ∧
      Bosonize.A06.branchMargins 8 2 0 Bosonize.Ch18.concreteNs Bosonize.Ch18.concreteBranches ∧
      Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs)
        (Bosonize.A05.rho 8 0 (-2) * Bosonize.A05.rho 8 0 2) = 2 ∧
      Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs)
        (Bosonize.A07Interactions.bogoliubovCreator 8 2
          Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s
          Bosonize.Ch18.concreteBranches .right *
         Bosonize.A07Interactions.bogoliubovAnnihilator 8 2
          Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s
          Bosonize.Ch18.concreteBranches .right) = (9 : ℂ) / 8 ∧
      Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs)
        (Bosonize.A07Interactions.bogoliubovCreator 8 2
          Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s
          Bosonize.Ch18.concreteBranches .right *
         Bosonize.A07Interactions.bogoliubovAnnihilator 8 2
          Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s
          Bosonize.Ch18.concreteBranches .right) ≠ 0 ∧
      Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs)
        (fockDensityR 8 2 (Bosonize.A01.canonicalRoot (2 * 8)) Bosonize.Ch18.concreteBranches 0 *
         fockDensityR 8 2 (Bosonize.A01.canonicalRoot (2 * 8)) Bosonize.Ch18.concreteBranches 0) =
        (3 : ℂ) / 256 := by
  have hN : Bosonize.A05.admissible 8 Bosonize.Ch18.concreteNs := by
    intro ν
    dsimp [Bosonize.A05.admissible, Bosonize.Ch18.concreteNs, Bosonize.Ch07.admissible]
    constructor <;> omega
  have hmar : Bosonize.A06.branchMargins 8 2 0 Bosonize.Ch18.concreteNs Bosonize.Ch18.concreteBranches := by
    constructor <;> norm_num [Bosonize.A06.branchMargins, Bosonize.A06.marginAt, Bosonize.Ch18.concreteNs, Bosonize.Ch18.concreteBranches, Bosonize.Ch16.standardBranches]
  have hroot : Bosonize.A01.canonicalRoot (2 * 8) ≠ 0 := by
    apply Bosonize.A01.root_ne_zero (2 * 8) (Bosonize.A01.canonicalRoot (2 * 8))
    exact Bosonize.A01.canonical_root_primitive (2 * 8)
  have hp_c_real : Bosonize.Ch18.concretePair.c = 5 / 4 := rfl
  have hp_s_real : Bosonize.Ch18.concretePair.s = 3 / 4 := rfl
  have hp_c : (Bosonize.Ch18.concretePair.c : ℂ) = 5 / 4 := by
    rw [hp_c_real]
    push_cast
    rfl
  have hp_s : (Bosonize.Ch18.concretePair.s : ℂ) = 3 / 4 := by
    rw [hp_s_real]
    push_cast
    rfl
  have h1 : Bosonize.A08.omegaP 2 Bosonize.Ch18.concretePair
      (Bosonize.A08.creatorGen 2 .right (1 : Fin 2) *
       Bosonize.A08.annihilatorGen 2 .right (1 : Fin 2)) = (9 : ℂ) / 8 := by
    rw [omegaP_creator_annihilator_right 2 Bosonize.Ch18.concretePair 1 1]
    simp only [ite_true]
    change ((1 + 1 : ℕ) : ℂ) * (Bosonize.Ch18.concretePair.s : ℂ) ^ 2 = _
    rw [hp_s]
    ring
  have h2 : Bosonize.A08.omegaP 2 Bosonize.Ch18.concretePair
      (Bosonize.A08.annihilatorGen 2 .right (1 : Fin 2) *
       Bosonize.A08.creatorGen 2 .right (1 : Fin 2)) = (25 : ℂ) / 8 := by
    rw [omegaP_annihilator_creator_right 2 Bosonize.Ch18.concretePair 1 1]
    simp only [ite_true]
    change ((1 + 1 : ℕ) : ℂ) * (Bosonize.Ch18.concretePair.c : ℂ) ^ 2 = _
    rw [hp_c]
    ring
  have h3 : Bosonize.A08.omegaP 2 Bosonize.Ch18.concretePair
      (Bosonize.A08.creatorGen 2 .right (1 : Fin 2) *
       Bosonize.A08.creatorGen 2 .left (1 : Fin 2)) = -(15 : ℂ) / 8 := by
    rw [omegaP_cross_creator_creator 2 Bosonize.Ch18.concretePair 1 1]
    simp only [ite_true]
    change -(((1 + 1 : ℕ) : ℂ) * (Bosonize.Ch18.concretePair.c : ℂ) * (Bosonize.Ch18.concretePair.s : ℂ)) = _
    rw [hp_c, hp_s]
    ring
  have h4 : orderedDensityCorrelation 8 2 (Bosonize.A01.canonicalRoot (2 * 8))
      Bosonize.Ch18.concretePair 0 0 = (51 : ℂ) / 2048 := by
    rw [ordered_density_kernel 8 2 (Bosonize.A01.canonicalRoot (2 * 8)) hroot Bosonize.Ch18.concretePair 0 0]
    unfold densityKernel
    simp only [sub_self]
    have hIcc : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
    rw [hIcc, Finset.sum_pair (by decide)]
    simp only [Bosonize.A01.integerCharacter, mul_zero, zpow_zero, mul_one]
    push_cast
    rw [hp_c, hp_s]
    ring
  have h6 : Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs)
      (Bosonize.A05.rho 8 0 (-2) * Bosonize.A05.rho 8 0 2) = 2 := by
    have hg := ground_lowering_raising 8 2 (by omega) 2 2 (by omega) (by omega) (by omega)
      Bosonize.Ch18.concreteBranches Bosonize.Ch18.concreteNs hN hmar.1
    have hright : Bosonize.Ch18.concreteBranches.rightSpecies = 0 := by rfl
    rw [hright] at hg
    simpa using hg
  have h7 : Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs)
      (Bosonize.A07Interactions.bogoliubovCreator 8 2
        Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s
        Bosonize.Ch18.concreteBranches .right *
       Bosonize.A07Interactions.bogoliubovAnnihilator 8 2
        Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s
        Bosonize.Ch18.concreteBranches .right) = (9 : ℂ) / 8 := by
    rw [ground_dressed_number 8 2 2 (by omega) (by omega) (by omega) Bosonize.Ch18.concretePair
      Bosonize.Ch18.concreteBranches .right Bosonize.Ch18.concreteNs hN hmar]
    push_cast
    rw [hp_s]
    ring
  have h8 : Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs)
      (Bosonize.A07Interactions.bogoliubovCreator 8 2
        Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s
        Bosonize.Ch18.concreteBranches .right *
       Bosonize.A07Interactions.bogoliubovAnnihilator 8 2
        Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s
        Bosonize.Ch18.concreteBranches .right) ≠ 0 := by
    rw [h7]
    norm_num
  have h9 : Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs)
      (fockDensityR 8 2 (Bosonize.A01.canonicalRoot (2 * 8)) Bosonize.Ch18.concreteBranches 0 *
       fockDensityR 8 2 (Bosonize.A01.canonicalRoot (2 * 8)) Bosonize.Ch18.concreteBranches 0) =
      (3 : ℂ) / 256 := by
    rw [fock_ground_density_kernel 8 2 (by omega) (Bosonize.A01.canonicalRoot (2 * 8)) hroot
      Bosonize.Ch18.concreteBranches Bosonize.Ch18.concreteNs hN hmar.1 0 0]
    unfold densityKernel
    have hIcc : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
    rw [hIcc, Finset.sum_pair (by decide)]
    simp only [sub_self, Bosonize.A01.integerCharacter, mul_zero, zpow_zero, mul_one]
    push_cast
    ring
  exact ⟨h1, h2, h3, h4, hmar, h6, h7, h8, h9⟩

end Bosonize.Ch19
