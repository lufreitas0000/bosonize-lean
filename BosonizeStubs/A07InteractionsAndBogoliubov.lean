import Bosonize

namespace Bosonize.A07Interactions

open scoped BigOperators Classical

section ScalarAndSyntax

def seaIndicator (h : ℕ) (k : Ch01.Band (2 * h)) : ℂ :=
  if k.val ≤ 0 then 1 else 0

def creatorToSeaLetter (h : ℕ) (k : Ch01.Band (2 * h)) :
    Bool × Ch01.Band (2 * h) :=
  (decide (0 < k.val), k)

def annihilatorToSeaLetter (h : ℕ) (k : Ch01.Band (2 * h)) :
    Bool × Ch01.Band (2 * h) :=
  (decide (k.val ≤ 0), k)

def seaInversions (h : ℕ) : List (Bool × Ch01.Band (2 * h)) → ℕ
  | [] => 0
  | (true, _) :: rest => seaInversions h rest
  | (false, _) :: rest => (rest.filter (fun l => l.1)).length + seaInversions h rest

def bilinearWord (h : ℕ) (a b : Ch01.Band (2 * h)) :
    List (Bool × Ch01.Band (2 * h)) :=
  [creatorToSeaLetter h a, annihilatorToSeaLetter h b]

def quarticWord (h : ℕ) (a b c d : Ch01.Band (2 * h)) :
    List (Bool × Ch01.Band (2 * h)) :=
  [creatorToSeaLetter h a, annihilatorToSeaLetter h b,
   creatorToSeaLetter h c, annihilatorToSeaLetter h d]

def seaWickWeight (h M : ℕ) (k : Ch01.Band (2 * h)) : ℤ :=
  if k.val ≤ 0 then 1 + 2 * min (M : ℤ) (-k.val)
  else 1 + 2 * min (M : ℤ) (k.val - 1)

def oppositeOrientation : A06.Orientation → A06.Orientation
  | .right => .left
  | .left => .right

structure HyperbolicParams (v1 v2 : ℝ) where
  u : ℝ
  c : ℝ
  s : ℝ
  u_pos : 0 < u
  c_pos : 0 < c
  u_sq : u ^ 2 = v1 ^ 2 - v2 ^ 2
  hyperbolic_id : c ^ 2 - s ^ 2 = 1
  match_v1 : v1 = u * (c ^ 2 + s ^ 2)
  match_v2 : v2 = 2 * u * c * s

theorem hyperbolic_params_exist (v1 v2 : ℝ) (hstab : |v2| < v1) :
    ∃ u c s : ℝ, 0 < u ∧ u ^ 2 = v1 ^ 2 - v2 ^ 2 ∧
      c ^ 2 - s ^ 2 = 1 ∧ v1 = u * (c ^ 2 + s ^ 2) ∧
      v2 = 2 * u * c * s := by sorry

end ScalarAndSyntax

section Operators

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable def seaQuasiAnnihilator (h : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) : A05.Operators σ h :=
  if k.val ≤ 0 then A05.creation h ν k else A05.annihilation h ν k

noncomputable def seaQuasiCreator (h : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) : A05.Operators σ h :=
  if k.val ≤ 0 then A05.annihilation h ν k else A05.creation h ν k

noncomputable def evalSeaLetter (h : ℕ) (ν : σ)
    (l : Bool × Ch01.Band (2 * h)) : A05.Operators σ h :=
  if l.1 then seaQuasiCreator h ν l.2 else seaQuasiAnnihilator h ν l.2

noncomputable def seaWickWord (h : ℕ) (ν : σ)
    (w : List (Bool × Ch01.Band (2 * h))) : A05.Operators σ h :=
  let creators := w.filter (fun l => l.1)
  let annihilators := w.filter (fun l => !l.1)
  ((-1 : ℂ) ^ seaInversions h w) •
    (((creators ++ annihilators).map (evalSeaLetter h ν)).prod)

noncomputable def numberOp (h : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) : A05.Operators σ h :=
  A05.creation h ν k * A05.annihilation h ν k

noncomputable def seaSubtractedNumber (h : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) : A05.Operators σ h :=
  numberOp h ν k - seaIndicator h k • (1 : A05.Operators σ h)

noncomputable def seaNormalBilinear (h : ℕ) (ν : σ)
    (a b : Ch01.Band (2 * h)) : A05.Operators σ h :=
  A05.creation h ν a * A05.annihilation h ν b -
    (if a = b then seaIndicator h a else 0) • (1 : A05.Operators σ h)

noncomputable def seaNormalRho (h : ℕ) (ν : σ) (m : ℤ) :
    A05.Operators σ h :=
  ∑ z ∈ A04.validPairs (2 * h) m, seaNormalBilinear h ν z.1 z.2

noncomputable def quarticSeaWick (h : ℕ) (ν : σ)
    (a b c d : Ch01.Band (2 * h)) : A05.Operators σ h :=
  seaWickWord h ν (quarticWord h a b c d)

noncomputable def quarticContraction (h : ℕ) (ν : σ)
    (k p : Ch01.Band (2 * h)) : A05.Operators σ h :=
  seaIndicator h p • seaSubtractedNumber h ν k -
    (1 - seaIndicator h k) • seaSubtractedNumber h ν p -
    (seaIndicator h p * (1 - seaIndicator h k)) • (1 : A05.Operators σ h)

noncomputable def seaWickTerm (h M : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) : A05.Operators σ h :=
  if k.val ≤ 0 then
    (seaWickWeight h M k : ℂ) • ((1 : A05.Operators σ h) - numberOp h ν k)
  else
    (seaWickWeight h M k : ℂ) • numberOp h ν k

noncomputable def seaWickCorrection (h M : ℕ) (ν : σ) :
    A05.Operators σ h :=
  ∑ k : Ch01.Band (2 * h), seaWickTerm h M ν k

noncomputable def computationalMomentum (h : ℕ) (ν : σ) :
    A05.Operators σ h :=
  ∑ k : Ch01.Band (2 * h), (k.val : ℂ) • seaSubtractedNumber h ν k

noncomputable def speciesRawIntra (h M : ℕ) (ν : σ) :
    A05.Operators σ h :=
  ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
    ∑ z ∈ A04.validPairs (2 * h) m,
      ∑ w ∈ A04.validPairs (2 * h) (-m),
        quarticSeaWick h ν z.1 z.2 w.1 w.2

noncomputable def rawIntraBranch (h M : ℕ) (g4 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  ((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) •
    (speciesRawIntra h M branches.rightSpecies +
      speciesRawIntra h M branches.leftSpecies)

noncomputable def speciesCurrentIntra (h M : ℕ) (ν : σ) :
    A05.Operators σ h :=
  (2 : ℂ) • (∑ m ∈ Finset.Icc 1 M,
    A05.rho h ν (m : ℤ) * A05.rho h ν (-(m : ℤ))) +
    A05.chargeObservable h ν * A05.chargeObservable h ν

noncomputable def currentIntraBranch (h M : ℕ) (g4 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  ((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) •
    (speciesCurrentIntra h M branches.rightSpecies +
      speciesCurrentIntra h M branches.leftSpecies)

noncomputable def rawInterBranch (h M : ℕ) (g2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  ((g2 : ℂ) / ((2 * h : ℕ) : ℂ)) •
    ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      seaNormalRho h branches.rightSpecies m *
        seaNormalRho h branches.leftSpecies (-m)

noncomputable def hoppingInterBranch (h M : ℕ) (g2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  ((g2 : ℂ) / ((2 * h : ℕ) : ℂ)) •
    (A05.chargeObservable h r * A05.chargeObservable h l +
      ∑ m ∈ Finset.Icc 1 M,
        (A05.rho h r (m : ℤ) * A05.rho h l (-(m : ℤ)) +
          A05.rho h r (-(m : ℤ)) * A05.rho h l (m : ℤ)))

noncomputable def pairingInterBranch (h M : ℕ) (g2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  ((g2 : ℂ) / ((2 * h : ℕ) : ℂ)) •
    (A05.chargeObservable h r * A05.chargeObservable h l +
      ∑ m ∈ Finset.Icc 1 M,
        (A05.rho h r (m : ℤ) * A05.rho h l (m : ℤ) +
          A05.rho h r (-(m : ℤ)) * A05.rho h l (-(m : ℤ))))

noncomputable def hoppingMode (h m : ℕ) (v1 v2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  (v1 : ℂ) • (A05.rho h r (m : ℤ) * A05.rho h r (-(m : ℤ)) +
    A05.rho h l (m : ℤ) * A05.rho h l (-(m : ℤ))) +
  (v2 : ℂ) • (A05.rho h r (m : ℤ) * A05.rho h l (-(m : ℤ)) +
    A05.rho h l (m : ℤ) * A05.rho h r (-(m : ℤ)))

noncomputable def pairingMode (h m : ℕ) (v1 v2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  (v1 : ℂ) • (A05.rho h r (m : ℤ) * A05.rho h r (-(m : ℤ)) +
    A05.rho h l (m : ℤ) * A05.rho h l (-(m : ℤ))) +
  (v2 : ℂ) • (A05.rho h r (m : ℤ) * A05.rho h l (m : ℤ) +
    A05.rho h r (-(m : ℤ)) * A05.rho h l (-(m : ℤ)))

noncomputable def bogoliubovCreator (h m : ℕ) (c s : ℝ)
    (branches : A06.Branches σ) (η : A06.Orientation) :
    A05.Operators σ h :=
  (c : ℂ) • A05.rho h (A06.speciesOf branches η) (m : ℤ) +
    (s : ℂ) • A05.rho h (A06.speciesOf branches (oppositeOrientation η)) (-(m : ℤ))

noncomputable def bogoliubovAnnihilator (h m : ℕ) (c s : ℝ)
    (branches : A06.Branches σ) (η : A06.Orientation) :
    A05.Operators σ h :=
  (c : ℂ) • A05.rho h (A06.speciesOf branches η) (-(m : ℤ)) +
    (s : ℂ) • A05.rho h (A06.speciesOf branches (oppositeOrientation η)) (m : ℤ)

noncomputable def dressedModeNumber (h m : ℕ) (u c s : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  (u : ℂ) • (bogoliubovCreator h m c s branches .right *
      bogoliubovAnnihilator h m c s branches .right +
    bogoliubovCreator h m c s branches .left *
      bogoliubovAnnihilator h m c s branches .left)

lemma sea_normal_bilinear_diag (h : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) :
    seaNormalBilinear h ν k k =
      if k.val ≤ 0 then -(A05.annihilation h ν k * A05.creation h ν k)
      else A05.creation h ν k * A05.annihilation h ν k := by sorry

lemma sea_normal_rho_nonzero (h : ℕ) (ν : σ) (m : ℤ) (hm : m ≠ 0) :
    seaNormalRho h ν m = A05.rho h ν m := by sorry

lemma sea_normal_rho_zero (h : ℕ) (ν : σ) :
    seaNormalRho h ν 0 = A05.chargeObservable h ν := by sorry

lemma quartic_sea_wick_identity (h : ℕ) (ν : σ) (m : ℤ)
    (z w : Ch01.Band (2 * h) × Ch01.Band (2 * h))
    (hz : z ∈ A04.validPairs (2 * h) m)
    (hw : w ∈ A04.validPairs (2 * h) (-m)) :
    quarticSeaWick h ν z.1 z.2 w.1 w.2 =
      seaNormalBilinear h ν z.1 z.2 * seaNormalBilinear h ν w.1 w.2 +
        if w.2 = z.1 then quarticContraction h ν z.2 w.2 else 0 := by sorry

lemma quartic_sea_wick_zero_repeated (h : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) :
    quarticSeaWick h ν k k k k = 0 ∧
      seaNormalBilinear h ν k k * seaNormalBilinear h ν k k +
        quarticContraction h ν k k = 0 := by sorry

lemma species_raw_intra_eq_current_sub_correction (h M : ℕ) (ν : σ) :
    speciesRawIntra h M ν =
      speciesCurrentIntra h M ν - seaWickCorrection h M ν := by sorry

theorem raw_intra_eq_current_sub_correction (h M : ℕ) (g4 : ℝ)
    (branches : A06.Branches σ) :
    rawIntraBranch h M g4 branches =
      currentIntraBranch h M g4 branches -
        ((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) •
          (seaWickCorrection h M branches.rightSpecies +
            seaWickCorrection h M branches.leftSpecies) := by sorry

lemma sea_wick_correction_ground_zero (h M : ℕ) (hh : 0 < h) (ν : σ) :
    seaWickCorrection h M ν (A05.groundKet h (fun _ : σ => 0)) = 0 := by sorry

lemma sea_wick_correction_full_band (h M : ℕ) (hh : 0 < h)
    (hM : h - 1 ≤ M) (ν : σ) :
    seaWickCorrection h M ν =
      (2 : ℂ) • computationalMomentum h ν - A05.chargeObservable h ν := by sorry

theorem raw_inter_eq_hopping (h M : ℕ) (g2 : ℝ)
    (branches : A06.Branches σ) :
    rawInterBranch h M g2 branches =
      hoppingInterBranch h M g2 branches := by sorry

lemma hopping_mode_kills_ground (h m : ℕ) (hh : 0 < h) (hm : 1 ≤ m)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (branches : A06.Branches σ) :
    (A05.rho h branches.rightSpecies (m : ℤ) *
        A05.rho h branches.leftSpecies (-(m : ℤ)) +
      A05.rho h branches.rightSpecies (-(m : ℤ)) *
        A05.rho h branches.leftSpecies (m : ℤ))
      (A05.groundKet h Ns) = 0 := by sorry

lemma pairing_mode_ground_nonzero (h M m : ℕ) (hh : 0 < h)
    (hm : 1 ≤ m) (hcut : m ≤ M) (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (branches : A06.Branches σ)
    (hmargin : A06.branchMargins h M m Ns branches) :
    (A05.rho h branches.rightSpecies (m : ℤ) *
        A05.rho h branches.leftSpecies (m : ℤ) +
      A05.rho h branches.rightSpecies (-(m : ℤ)) *
        A05.rho h branches.leftSpecies (-(m : ℤ)))
      (A05.groundKet h Ns) ≠ 0 := by sorry

lemma hopping_mode_self_adjoint (h m : ℕ) (v1 v2 : ℝ)
    (branches : A06.Branches σ) :
    LinearMap.adjoint (hoppingMode h m v1 v2 branches) =
      hoppingMode h m v1 v2 branches := by sorry

lemma pairing_mode_self_adjoint (h m : ℕ) (v1 v2 : ℝ)
    (branches : A06.Branches σ) :
    LinearMap.adjoint (pairingMode h m v1 v2 branches) =
      pairingMode h m v1 v2 branches := by sorry

lemma bogoliubov_creator_adjoint (h m : ℕ) (c s : ℝ)
    (branches : A06.Branches σ) (η : A06.Orientation) :
    LinearMap.adjoint (bogoliubovCreator h m c s branches η) =
      bogoliubovAnnihilator h m c s branches η := by sorry

theorem bogoliubov_expansion_on_budget (h M K m : ℕ) (hh : 0 < h)
    (hm : 1 ≤ m) (hcut : m ≤ M) (v1 v2 : ℝ)
    (hp : HyperbolicParams v1 v2) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    dressedModeNumber h m hp.u hp.c hp.s branches v =
      pairingMode h m v1 v2 branches v +
        ((2 * hp.u * hp.s ^ 2 * (m : ℝ) : ℝ) : ℂ) • v := by sorry

theorem bogoliubov_ccr_on_budget (h M K m : ℕ) (hh : 0 < h)
    (hm : 1 ≤ m) (hcut : m ≤ M) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1)
    (branches : A06.Branches σ) (η : A06.Orientation)
    (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator
        (bogoliubovAnnihilator h m c s branches η)
        (bogoliubovCreator h m c s branches η) v =
      (m : ℂ) • v := by sorry

end Operators

end Bosonize.A07Interactions
