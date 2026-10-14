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
      v2 = 2 * u * c * s := by
  have hlt := abs_lt.mp hstab
  have hv1 : 0 < v1 := by linarith [hlt.1, hlt.2]
  have hpos : 0 < v1 ^ 2 - v2 ^ 2 := by
    have h1 : 0 < v1 - v2 := by linarith [hlt.2]
    have h2 : 0 < v1 + v2 := by linarith [hlt.1]
    have e : v1 ^ 2 - v2 ^ 2 = (v1 - v2) * (v1 + v2) := by ring
    rw [e]
    exact mul_pos h1 h2
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = Real.sqrt (v1 ^ 2 - v2 ^ 2) := ⟨_, rfl⟩
  have hu : 0 < u := by rw [hu_def]; exact Real.sqrt_pos.mpr hpos
  have hu2 : u ^ 2 = v1 ^ 2 - v2 ^ 2 := by rw [hu_def]; exact Real.sq_sqrt hpos.le
  have hu0 : u ≠ 0 := hu.ne'
  have h2u : (2 : ℝ) * u ≠ 0 := (mul_pos (by norm_num) hu).ne'
  have hv1u : 0 < v1 + u := by linarith [hv1, hu]
  have hcarg : 0 < (v1 + u) / (2 * u) := div_pos hv1u (mul_pos (by norm_num) hu)
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = Real.sqrt ((v1 + u) / (2 * u)) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hc_def]; exact Real.sqrt_pos.mpr hcarg
  have hc2 : c ^ 2 = (v1 + u) / (2 * u) := by rw [hc_def]; exact Real.sq_sqrt hcarg.le
  have hc0 : c ≠ 0 := hc.ne'
  have hc2' : c ^ 2 * (2 * u) = v1 + u := by rw [hc2]; field_simp
  have hv2 : v2 ^ 2 = (v1 - u) * (v1 + u) := by nlinarith [hu2]
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = v2 / (2 * u * c) := ⟨_, rfl⟩
  have key : s * (2 * u * c) = v2 := by rw [hs_def]; field_simp
  have hs2 : s ^ 2 * (2 * u) = v1 - u := by
    have hk : (s * (2 * u * c)) ^ 2 = v2 ^ 2 := by rw [key]
    have e : (s * (2 * u * c)) ^ 2 = (s ^ 2 * (2 * u)) * (c ^ 2 * (2 * u)) := by ring
    rw [e, hc2'] at hk
    have h1 : (s ^ 2 * (2 * u)) * (v1 + u) = (v1 - u) * (v1 + u) := hk.trans hv2
    exact mul_right_cancel₀ hv1u.ne' h1
  refine ⟨u, c, s, hu, hu2, ?_, ?_, ?_⟩
  · have h1 : (c ^ 2 - s ^ 2) * (2 * u) = 1 * (2 * u) := by nlinarith [hc2', hs2]
    exact mul_right_cancel₀ h2u h1
  · nlinarith [hc2', hs2]
  · rw [← key]; ring

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
      else A05.creation h ν k * A05.annihilation h ν k := by
  have hcar := A05.mixed_car h (ν, k) (ν, k)
  simp only [A02.anticommutator, ite_true, one_smul] at hcar
  by_cases hk : k.val ≤ 0
  · simp only [seaNormalBilinear, seaIndicator, hk, ite_true, one_smul]
    rw [eq_sub_of_add_eq hcar]
    abel
  · simp [seaNormalBilinear, seaIndicator, hk]

lemma sea_normal_rho_nonzero (h : ℕ) (ν : σ) (m : ℤ) (hm : m ≠ 0) :
    seaNormalRho h ν m = A05.rho h ν m := by
  unfold seaNormalRho A05.rho
  apply Finset.sum_congr rfl
  intro z hz
  have he := (A04.mem_valid_pairs (2 * h) m z.1 z.2).mp hz
  have hne : z.1 ≠ z.2 := by
    intro hz
    rw [hz] at he
    omega
  simp only [seaNormalBilinear, hne, ite_false, zero_smul, sub_zero,
    Ch04.hopping, A05.creation, A05.annihilation]

lemma sea_normal_rho_zero (h : ℕ) (ν : σ) :
    seaNormalRho h ν 0 = A05.chargeObservable h ν := by
  have hdiag : seaNormalRho h ν 0 =
      ∑ k : Ch01.Band (2 * h), seaSubtractedNumber h ν k := by
    unfold seaNormalRho
    have hz (z : Ch01.Band (2 * h) × Ch01.Band (2 * h))
        (hz : z ∈ A04.validPairs (2 * h) 0) : z.1 = z.2 := by
      have he := (A04.mem_valid_pairs (2 * h) 0 z.1 z.2).mp hz
      apply Subtype.ext
      omega
    apply Finset.sum_bij (fun z _ => z.1)
    · intro z hz
      exact Finset.mem_univ _
    · intro z hZ w hw he
      apply Prod.ext
      · exact he
      · exact (hz z hZ).symm.trans (he.trans (hz w hw))
    · intro k hk
      refine ⟨(k,k), ?_, rfl⟩
      apply (A04.mem_valid_pairs (2 * h) 0 k k).mpr
      simp
    · intro z hZ
      rw [hz z hZ]
      simp only [seaNormalBilinear, seaSubtractedNumber, numberOp, ite_true]
  rw [hdiag]
  let : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
  let : DecidableEq (A05.Mode σ h) := fun a b => (A05.speciesOrder h).toDecidableEq a b
  apply A02.end_ext_basis
  intro S
  have hmem (k : Ch01.Band (2 * h)) :
      k ∈ Ch07.speciesConfiguration h S ν ↔ (ν,k) ∈ S := by
    simp only [Ch07.speciesConfiguration, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨η,l⟩, ⟨hS, hη⟩, hl⟩
      dsimp at hη hl
      subst η
      subst l
      exact hS
    · intro hk
      exact ⟨(ν,k), ⟨hk,rfl⟩,rfl⟩
  have hcount : (∑ k : Ch01.Band (2 * h),
      if (ν,k) ∈ S then (1 : ℂ) else 0) =
      ((Ch07.speciesConfiguration h S ν).card : ℂ) := by
    simp only [← hmem]
    simp
  have hsea : (∑ k : Ch01.Band (2 * h), seaIndicator h k) = (h : ℂ) := by
    have hcard : (Ch05.seaConfiguration (2 * h)).card = h := by
      by_cases hh : 0 < h
      · exact Ch05.sea_card_even h hh
      · have hh0 : h = 0 := by omega
        subst h
        let : IsEmpty (Ch01.Band (2 * 0)) := ⟨fun k => by
          have hk := k.property
          norm_num [Ch01.inBandPredicate] at hk
          omega⟩
        simp [Ch05.seaConfiguration]
    simpa [seaIndicator, Ch05.seaConfiguration] using
      congrArg (fun n : ℕ => (n : ℂ)) hcard
  have hn (k : Ch01.Band (2 * h)) :
      numberOp h ν k (A02.ket S) = (if (ν,k) ∈ S then (1 : ℂ) else 0) • A02.ket S := by
    exact Ch04.number_ket (ν,k) S
  simp only [LinearMap.sum_apply, seaSubtractedNumber, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, hn,
    A05.chargeObservable, A03.diagonal_ket, ← sub_smul, ← Finset.sum_smul]
  rw [Finset.sum_sub_distrib, hcount, hsea]
  simp only [Ch07.relativeCharge, Int.cast_sub, Int.cast_natCast]


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
        quarticContraction h ν k k = 0 := by
  let : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
  have hc0 : A05.creation h ν k * A05.creation h ν k = 0 := by
    exact Ch04.creation_square (ν, k)
  have ha0 : A05.annihilation h ν k * A05.annihilation h ν k = 0 := by
    exact Ch04.annihilation_square (ν, k)
  have hn : numberOp h ν k * numberOp h ν k = numberOp h ν k := by
    exact Ch04.number_idempotent (ν, k)
  constructor
  · by_cases hk : k.val ≤ 0
    all_goals
      simp [quarticSeaWick, seaWickWord, quarticWord, creatorToSeaLetter,
        annihilatorToSeaLetter, seaInversions, evalSeaLetter, seaQuasiCreator,
        seaQuasiAnnihilator, hk, show (0 < k.val) ↔ ¬ k.val ≤ 0 by omega,
        hc0, ha0]
  · by_cases hk : k.val ≤ 0
    all_goals
      simp only [seaNormalBilinear, quarticContraction, seaSubtractedNumber,
        seaIndicator, hk, ite_true, ite_false, one_smul, zero_smul]
      change (numberOp h ν k - _) * (numberOp h ν k - _) + _ = 0
      simp only [sub_mul, mul_sub, mul_one, one_mul, hn, smul_sub,
        sub_self, sub_zero, zero_sub, zero_smul, one_smul]
      module

lemma species_raw_intra_eq_current_sub_correction (h M : ℕ) (ν : σ) :
    speciesRawIntra h M ν =
      speciesCurrentIntra h M ν - seaWickCorrection h M ν := by
  classical
  have hflip (m : ℤ) (f : (Ch01.Band (2*h) × Ch01.Band (2*h)) → A05.Operators σ h) :
      (∑ z ∈ A04.validPairs (2*h) (-m), f z) =
        ∑ z ∈ A04.validPairs (2*h) m, f (z.2,z.1) := by
    apply Finset.sum_bij (fun z _ => (z.2,z.1))
    · intro z hz
      rw [A04.mem_valid_pairs] at hz ⊢
      omega
    · intro z hz w hw he
      exact Prod.swap_injective he
    · intro z hz
      refine ⟨(z.2,z.1), ?_, rfl⟩
      rw [A04.mem_valid_pairs] at hz ⊢
      omega
    · intro z hz
      rfl
  have hcon (m : ℤ) (z : Ch01.Band (2*h) × Ch01.Band (2*h))
      (hz : z ∈ A04.validPairs (2*h) m) :
      (∑ w ∈ A04.validPairs (2*h) (-m),
        if w.2 = z.1 then quarticContraction h ν z.2 w.2 else 0) =
        quarticContraction h ν z.2 z.1 := by
    rw [Finset.sum_eq_single (z.2,z.1)]
    · simp
    · intro w hw he
      have hne : w.2 ≠ z.1 := by
        intro eq
        apply he
        apply Prod.ext
        · apply Subtype.ext
          change w.1.val = z.2.val
          have h1 := (A04.mem_valid_pairs _ _ _ _).mp hz
          have h2 := (A04.mem_valid_pairs _ _ _ _).mp hw
          have h3 := congrArg Subtype.val eq
          omega
        · exact eq
      simp only [hne, ite_false]
    · intro hnot
      have hf : (z.2,z.1) ∈ A04.validPairs (2*h) (-m) := by
        rw [A04.mem_valid_pairs] at hz ⊢
        omega
      exact False.elim (hnot hf)
  have hraw (m : ℤ) :
      (∑ z ∈ A04.validPairs (2*h) m,
        ∑ w ∈ A04.validPairs (2*h) (-m), quarticSeaWick h ν z.1 z.2 w.1 w.2) =
      seaNormalRho h ν m * seaNormalRho h ν (-m) +
        ∑ z ∈ A04.validPairs (2*h) m, quarticContraction h ν z.2 z.1 := by
    calc
      _ = ∑ z ∈ A04.validPairs (2*h) m,
          ∑ w ∈ A04.validPairs (2*h) (-m),
            (seaNormalBilinear h ν z.1 z.2 * seaNormalBilinear h ν w.1 w.2 +
              if w.2 = z.1 then quarticContraction h ν z.2 w.2 else 0) := by
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro w hw
        exact quartic_sea_wick_identity h ν m z w hz hw
      _ = _ := by
        simp_rw [Finset.sum_add_distrib]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro z hz
        exact hcon m z hz
  have hedge (m : ℤ) :
      A02.commutator (A05.rho h ν (-m)) (A05.rho h ν m) =
        ∑ z ∈ A04.validPairs (2*h) m, (numberOp h ν z.2 - numberOp h ν z.1) := by
    let : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
    unfold A05.rho
    rw [hflip]
    have hbilin (s t : Finset (Ch01.Band (2*h) × Ch01.Band (2*h))) :
        A02.commutator (∑ z ∈ s, Ch04.hopping (ν,z.2) (ν,z.1))
          (∑ w ∈ t, Ch04.hopping (ν,w.1) (ν,w.2)) =
        ∑ z ∈ s, ∑ w ∈ t,
          A02.commutator (Ch04.hopping (ν,z.2) (ν,z.1)) (Ch04.hopping (ν,w.1) (ν,w.2)) := by
      simp only [A02.commutator, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
    rw [hbilin]
    apply Finset.sum_congr rfl
    intro z hz
    rw [Finset.sum_eq_single z]
    · simp only [Ch04.bilinear_commutator, ite_true, one_smul]
      rfl
    · intro w hw he
      have hf : z.1 ≠ w.1 := by
        intro eq
        apply he
        apply Prod.ext
        · exact eq.symm
        · apply Subtype.ext
          have h1 := (A04.mem_valid_pairs _ _ _ _).mp hz
          have h2 := (A04.mem_valid_pairs _ _ _ _).mp hw
          have h3 := congrArg Subtype.val eq
          omega
      have hs : z.2 ≠ w.2 := by
        intro eq
        apply he
        apply Prod.ext
        · apply Subtype.ext
          have h1 := (A04.mem_valid_pairs _ _ _ _).mp hz
          have h2 := (A04.mem_valid_pairs _ _ _ _).mp hw
          have h3 := congrArg Subtype.val eq
          omega
        · exact eq.symm
      simp only [Ch04.bilinear_commutator, Prod.mk.injEq, true_and, hf, hs,
        ite_false, zero_smul, sub_self]
    · intro hnot
      exact False.elim (hnot hz)
  have hdelta (a b : Ch01.Band (2*h)) (hab : b.val < a.val) :
      (numberOp h ν b - numberOp h ν a) + quarticContraction h ν b a +
        quarticContraction h ν a b =
      (-2 : ℂ) • ((if a.val ≤ 0 then (1 : A05.Operators σ h) - numberOp h ν b else 0) +
        (if 0 < b.val then numberOp h ν a else 0)) := by
    by_cases ha : a.val ≤ 0 <;> by_cases hb : b.val ≤ 0
    all_goals try { omega }
    all_goals
      simp only [quarticContraction, seaSubtractedNumber, seaIndicator, ha, hb,
        show (0 < b.val) ↔ ¬ b.val ≤ 0 by omega, ite_true, ite_false,
        not_true_eq_false, not_false_eq_true, one_smul, zero_smul, sub_zero, sub_self, zero_mul, mul_zero, one_mul]
      module
  have hcount (D : ℤ) (hD : 0 ≤ D) (X : A05.Operators σ h) :
      (∑ n ∈ Finset.Icc 1 M, if (n : ℤ) ≤ D then X else 0) =
        ((min (M : ℤ) D : ℤ) : ℂ) • X := by
    have hf : (Finset.Icc 1 M).filter (fun n : ℕ => (n : ℤ) ≤ D) = Finset.Icc 1 (min M D.toNat) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
      have hd := Int.toNat_of_nonneg hD
      omega
    rw [← Finset.sum_filter, hf, Finset.sum_const]
    have hc : (Finset.Icc 1 (min M D.toNat)).card = min M D.toNat := by
      simp
    rw [hc, ← Nat.cast_smul_eq_nsmul ℂ]
    change ((min M D.toNat : ℕ) : ℂ) • X = _
    congr 1
    have he : ((min M D.toNat : ℕ) : ℤ) = min (M : ℤ) D := by
      rw [Nat.cast_min, Int.toNat_of_nonneg hD]
    simpa only [Int.cast_natCast] using congrArg (fun x : ℤ => (x : ℂ)) he
  have hholes (m : ℤ) (hm : 0 < m) (F : Ch01.Band (2*h) → A05.Operators σ h) :
      (∑ z ∈ A04.validPairs (2*h) m, if z.1.val ≤ 0 then F z.2 else 0) =
        ∑ k : Ch01.Band (2*h), if k.val ≤ -m then F k else 0 := by
    have he : (∑ z ∈ (A04.validPairs (2*h) m).filter (fun z => z.1.val ≤ 0), F z.2) =
        ∑ k ∈ Finset.univ.filter (fun k : Ch01.Band (2*h) => k.val ≤ -m), F k := by
      apply Finset.sum_bij (fun z _ => z.2)
      · intro z hz
        simp only [Finset.mem_filter] at hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have ha := (A04.mem_valid_pairs _ _ _ _).mp hz.1
        omega
      · intro z hz w hw he
        apply Prod.ext
        · apply Subtype.ext
          have hz' := (A04.mem_valid_pairs _ _ _ _).mp (Finset.mem_filter.mp hz).1
          have hw' := (A04.mem_valid_pairs _ _ _ _).mp (Finset.mem_filter.mp hw).1
          have hv := congrArg Subtype.val he
          omega
        · exact he
      · intro k hk
        have hk' := (Finset.mem_filter.mp hk).2
        let a : Ch01.Band (2*h) := ⟨k.val + m, by
          have hb := k.property
          unfold Ch01.inBandPredicate at hb ⊢
          omega⟩
        refine ⟨(a,k), ?_, rfl⟩
        simp only [Finset.mem_filter, A04.mem_valid_pairs]
        dsimp [a]
        constructor <;> omega
      · intro z hz
        rfl
    simpa only [Finset.sum_filter] using he
  have hparticles (m : ℤ) (hm : 0 < m) (F : Ch01.Band (2*h) → A05.Operators σ h) :
      (∑ z ∈ A04.validPairs (2*h) m, if 0 < z.2.val then F z.1 else 0) =
        ∑ k : Ch01.Band (2*h), if m < k.val then F k else 0 := by
    have he : (∑ z ∈ (A04.validPairs (2*h) m).filter (fun z => 0 < z.2.val), F z.1) =
        ∑ k ∈ Finset.univ.filter (fun k : Ch01.Band (2*h) => m < k.val), F k := by
      apply Finset.sum_bij (fun z _ => z.1)
      · intro z hz
        simp only [Finset.mem_filter] at hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have ha := (A04.mem_valid_pairs _ _ _ _).mp hz.1
        omega
      · intro z hz w hw he
        apply Prod.ext
        · exact he
        · apply Subtype.ext
          have hz' := (A04.mem_valid_pairs _ _ _ _).mp (Finset.mem_filter.mp hz).1
          have hw' := (A04.mem_valid_pairs _ _ _ _).mp (Finset.mem_filter.mp hw).1
          have hv := congrArg Subtype.val he
          omega
      · intro k hk
        have hk' := (Finset.mem_filter.mp hk).2
        let b : Ch01.Band (2*h) := ⟨k.val - m, by
          have hb := k.property
          unfold Ch01.inBandPredicate at hb ⊢
          omega⟩
        refine ⟨(k,b), ?_, rfl⟩
        simp only [Finset.mem_filter, A04.mem_valid_pairs]
        dsimp [b]
        constructor <;> omega
      · intro z hz
        rfl
    simpa only [Finset.sum_filter] using he
  let f (m : ℤ) : A05.Operators σ h :=
    ∑ z ∈ A04.validPairs (2*h) m, ∑ w ∈ A04.validPairs (2*h) (-m),
      quarticSeaWick h ν z.1 z.2 w.1 w.2
  let D (n : ℕ) : A05.Operators σ h :=
    (∑ k : Ch01.Band (2*h), if k.val ≤ -(n : ℤ) then (1 : A05.Operators σ h) - numberOp h ν k else 0) +
    (∑ k : Ch01.Band (2*h), if (n : ℤ) < k.val then numberOp h ν k else 0)
  have hpos (n : ℕ) (hn : 1 ≤ n) :
      f (n : ℤ) + f (-(n : ℤ)) =
        (2 : ℂ) • (A05.rho h ν (n : ℤ) * A05.rho h ν (-(n : ℤ))) - (2 : ℂ) • D n := by
    have hnz : (n : ℤ) ≠ 0 := by omega
    have hnpos : 0 < (n : ℤ) := by omega
    calc
      _ = A05.rho h ν (n : ℤ) * A05.rho h ν (-(n : ℤ)) +
          A05.rho h ν (-(n : ℤ)) * A05.rho h ν (n : ℤ) +
          ∑ z ∈ A04.validPairs (2*h) (n : ℤ),
            (quarticContraction h ν z.2 z.1 + quarticContraction h ν z.1 z.2) := by
        dsimp only [f]
        rw [hraw, hraw, neg_neg, hflip]
        rw [sea_normal_rho_nonzero h ν _ hnz, sea_normal_rho_nonzero h ν _ (neg_ne_zero.mpr hnz)]
        rw [Finset.sum_add_distrib]
        abel
      _ = (2 : ℂ) • (A05.rho h ν (n : ℤ) * A05.rho h ν (-(n : ℤ))) +
          ∑ z ∈ A04.validPairs (2*h) (n : ℤ),
            ((numberOp h ν z.2 - numberOp h ν z.1) +
              quarticContraction h ν z.2 z.1 + quarticContraction h ν z.1 z.2) := by
        simp only [Finset.sum_add_distrib]
        rw [← hedge]
        simp only [A02.commutator]
        module
      _ = _ := by
        have hs : (∑ z ∈ A04.validPairs (2*h) (n : ℤ),
            ((numberOp h ν z.2 - numberOp h ν z.1) +
              quarticContraction h ν z.2 z.1 + quarticContraction h ν z.1 z.2)) =
            (-2 : ℂ) • D n := by
          calc
            _ = ∑ z ∈ A04.validPairs (2*h) (n : ℤ),
              (-2 : ℂ) • ((if z.1.val ≤ 0 then (1 : A05.Operators σ h) - numberOp h ν z.2 else 0) +
                (if 0 < z.2.val then numberOp h ν z.1 else 0)) := by
              apply Finset.sum_congr rfl
              intro z hz
              apply hdelta
              have hb := (A04.mem_valid_pairs _ _ _ _).mp hz
              omega
            _ = _ := by
              rw [← Finset.smul_sum, Finset.sum_add_distrib, hholes _ hnpos (fun k => (1 : A05.Operators σ h) - numberOp h ν k), hparticles _ hnpos (fun k => numberOp h ν k)]
        rw [hs]
        module
  have hzeroCon : (∑ z ∈ A04.validPairs (2*h) 0, quarticContraction h ν z.2 z.1) =
      ∑ k : Ch01.Band (2*h), quarticContraction h ν k k := by
    apply Finset.sum_bij (fun z _ => z.1)
    · intro z hz
      exact Finset.mem_univ _
    · intro z hz w hw he
      apply Prod.ext
      · exact he
      · apply Subtype.ext
        have hz' := (A04.mem_valid_pairs _ _ _ _).mp hz
        have hw' := (A04.mem_valid_pairs _ _ _ _).mp hw
        have hh := congrArg Subtype.val he
        omega
    · intro k hk
      refine ⟨(k,k), ?_, rfl⟩
      rw [A04.mem_valid_pairs]
      omega
    · intro z hz
      have he : z.2 = z.1 := by
        apply Subtype.ext
        have hb := (A04.mem_valid_pairs _ _ _ _).mp hz
        omega
      rw [he]
  have hbaseweight (k : Ch01.Band (2*h)) : seaWickWeight h 0 k = 1 := by
    by_cases hk : k.val ≤ 0
    · simp [seaWickWeight, hk]
    · simp [seaWickWeight, hk, min_eq_left (by omega : (0 : ℤ) ≤ k.val-1)]
  have hbaseterm (k : Ch01.Band (2*h)) : seaWickTerm h 0 ν k =
      if k.val ≤ 0 then (1 : A05.Operators σ h) - numberOp h ν k else numberOp h ν k := by
    unfold seaWickTerm
    simp only [hbaseweight, Int.cast_one, one_smul]
  have hzterm (k : Ch01.Band (2*h)) : quarticContraction h ν k k = -seaWickTerm h 0 ν k := by
    by_cases hk : k.val ≤ 0
    all_goals
      simp only [quarticContraction, seaSubtractedNumber, seaIndicator,
        seaWickTerm, hbaseweight, hk, ite_true, ite_false, Int.cast_one,
        zero_mul, mul_zero,
        one_smul, zero_smul, sub_self, sub_zero]
      module
  have hzraw : f 0 = A05.chargeObservable h ν * A05.chargeObservable h ν - seaWickCorrection h 0 ν := by
    dsimp only [f]
    rw [hraw, neg_zero, sea_normal_rho_zero, hzeroCon]
    simp_rw [hzterm]
    rw [Finset.sum_neg_distrib]
    rfl
  have hterm (k : Ch01.Band (2*h)) :
      seaWickTerm h M ν k = seaWickTerm h 0 ν k + (2 : ℂ) •
        (∑ n ∈ Finset.Icc 1 M,
          ((if k.val ≤ -(n : ℤ) then (1 : A05.Operators σ h) - numberOp h ν k else 0) +
            (if (n : ℤ) < k.val then numberOp h ν k else 0))) := by
    by_cases hk : k.val ≤ 0
    · have hs : (∑ n ∈ Finset.Icc 1 M,
          ((if k.val ≤ -(n : ℤ) then (1 : A05.Operators σ h) - numberOp h ν k else 0) +
            (if (n : ℤ) < k.val then numberOp h ν k else 0))) =
          ∑ n ∈ Finset.Icc 1 M, if (n : ℤ) ≤ -k.val then (1 : A05.Operators σ h) - numberOp h ν k else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnp := (Finset.mem_Icc.mp hn).1
        have he : (k.val ≤ -(n : ℤ)) ↔ (n : ℤ) ≤ -k.val := by omega
        have hf : ¬ (n : ℤ) < k.val := by omega
        simp only [he, hf, ite_false, add_zero]
      rw [hs, hcount _ (by omega), hbaseterm]
      simp only [seaWickTerm, seaWickWeight, hk, ite_true, Int.cast_one,
        Int.cast_add, Int.cast_mul, Int.cast_ofNat]
      module
    · have hs : (∑ n ∈ Finset.Icc 1 M,
          ((if k.val ≤ -(n : ℤ) then (1 : A05.Operators σ h) - numberOp h ν k else 0) +
            (if (n : ℤ) < k.val then numberOp h ν k else 0))) =
          ∑ n ∈ Finset.Icc 1 M, if (n : ℤ) ≤ k.val-1 then numberOp h ν k else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnp := (Finset.mem_Icc.mp hn).1
        have he : ((n : ℤ) < k.val) ↔ (n : ℤ) ≤ k.val-1 := by omega
        have hf : ¬ k.val ≤ -(n : ℤ) := by omega
        simp only [he, hf, ite_false, zero_add]
      rw [hs, hcount _ (by omega), hbaseterm]
      simp only [seaWickTerm, seaWickWeight, hk, ite_false, Int.cast_one,
        Int.cast_add, Int.cast_mul, Int.cast_ofNat]
      module
  have hQ : seaWickCorrection h M ν = seaWickCorrection h 0 ν +
      (2 : ℂ) • ∑ n ∈ Finset.Icc 1 M, D n := by
    unfold seaWickCorrection
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, Finset.sum_comm]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.sum_add_distrib]
  have hsplit (N : ℕ) :
      (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f m) =
        f 0 + ∑ m ∈ Finset.Icc 1 N, (f (m : ℤ) + f (-(m : ℤ))) := by
    induction N with
    | zero => simp
    | succ n ih =>
      have hi : Finset.Icc (-((n+1 : ℕ) : ℤ)) ((n+1 : ℕ) : ℤ) =
          insert (-((n+1 : ℕ) : ℤ)) (insert ((n+1 : ℕ) : ℤ) (Finset.Icc (-(n : ℤ)) (n : ℤ))) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
        omega
      have hn : Finset.Icc 1 (n+1) = insert (n+1) (Finset.Icc 1 n) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hp : ((n+1 : ℕ) : ℤ) ∉ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
        simp only [Finset.mem_Icc, Nat.cast_add, Nat.cast_one]
        omega
      have hm : -((n+1 : ℕ) : ℤ) ∉ insert ((n+1 : ℕ) : ℤ) (Finset.Icc (-(n : ℤ)) (n : ℤ)) := by
        simp only [Finset.mem_Icc, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
        omega
      have hnp : n+1 ∉ Finset.Icc 1 n := by simp
      rw [hi, hn, Finset.sum_insert hm, Finset.sum_insert hp, Finset.sum_insert hnp, ih]
      abel
  change (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f m) = _
  rw [hsplit, hzraw]
  have hpairs : (∑ n ∈ Finset.Icc 1 M, (f (n : ℤ) + f (-(n : ℤ)))) =
      (2 : ℂ) • (∑ n ∈ Finset.Icc 1 M,
        A05.rho h ν (n : ℤ) * A05.rho h ν (-(n : ℤ))) - (2 : ℂ) • ∑ n ∈ Finset.Icc 1 M, D n := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    exact hpos n (Finset.mem_Icc.mp hn).1
  rw [hpairs, hQ]
  unfold speciesCurrentIntra
  abel

theorem raw_intra_eq_current_sub_correction (h M : ℕ) (g4 : ℝ)
    (branches : A06.Branches σ) :
    rawIntraBranch h M g4 branches =
      currentIntraBranch h M g4 branches -
        ((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) •
          (seaWickCorrection h M branches.rightSpecies +
            seaWickCorrection h M branches.leftSpecies)  := by
  unfold rawIntraBranch currentIntraBranch
  rw [species_raw_intra_eq_current_sub_correction,
    species_raw_intra_eq_current_sub_correction]
  module

lemma sea_wick_correction_ground_zero (h M : ℕ) (hh : 0 < h) (ν : σ) :
    seaWickCorrection h M ν (A05.groundKet h (fun _ : σ => 0)) = 0 := by
  let : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
  let : DecidableEq (A05.Mode σ h) := fun a b => (A05.speciesOrder h).toDecidableEq a b
  have _ := hh
  have hmem (k : Ch01.Band (2 * h)) :
      (ν, k) ∈ A05.groundConfiguration h (fun _ : σ => 0) ↔ k.val ≤ 0 := by
    simp [A05.groundConfiguration, A05.jointConfiguration, Ch07.groundConfiguration]
  unfold seaWickCorrection
  rw [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  have hn : numberOp h ν k (A05.groundKet h (fun _ : σ => 0)) =
      (if k.val ≤ 0 then (1 : ℂ) else 0) • A05.groundKet h (fun _ : σ => 0) := by
    change Ch04.number (ν, k) (A02.ket _) = _
    simp only [Ch04.number_ket, hmem, A05.groundKet]
  by_cases hc : k.val ≤ 0
  · simp only [seaWickTerm, hc, ite_true, LinearMap.smul_apply,
      LinearMap.sub_apply, Module.End.one_apply, hn, one_smul, sub_self, smul_zero]
  · simp only [seaWickTerm, hc, ite_false, LinearMap.smul_apply, hn, zero_smul, smul_zero]


lemma sea_wick_correction_full_band (h M : ℕ) (hh : 0 < h)
    (hM : h - 1 ≤ M) (ν : σ) :
    seaWickCorrection h M ν =
      (2 : ℂ) • computationalMomentum h ν - A05.chargeObservable h ν := by
  have hdiag : seaNormalRho h ν 0 =
      ∑ k : Ch01.Band (2 * h), seaSubtractedNumber h ν k := by
    unfold seaNormalRho
    have hz (z : Ch01.Band (2 * h) × Ch01.Band (2 * h))
        (hz : z ∈ A04.validPairs (2 * h) 0) : z.1 = z.2 := by
      have he := (A04.mem_valid_pairs (2 * h) 0 z.1 z.2).mp hz
      apply Subtype.ext
      omega
    apply Finset.sum_bij (fun z _ => z.1)
    · intro z hz
      exact Finset.mem_univ _
    · intro z hZ w hw he
      apply Prod.ext
      · exact he
      · exact (hz z hZ).symm.trans (he.trans (hz w hw))
    · intro k hk
      refine ⟨(k,k), ?_, rfl⟩
      apply (A04.mem_valid_pairs (2 * h) 0 k k).mpr
      simp
    · intro z hZ
      rw [hz z hZ]
      simp only [seaNormalBilinear, seaSubtractedNumber, numberOp, ite_true]
  rw [← sea_normal_rho_zero, hdiag]
  unfold seaWickCorrection computationalMomentum
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hb := k.property
  simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hb
  have hMm : (h : ℤ) - 1 ≤ (M : ℤ) := by omega
  by_cases hc : k.val ≤ 0
  · have hmin : min (M : ℤ) (-k.val) = -k.val := min_eq_right (by omega)
    simp only [seaWickTerm, seaWickWeight, seaSubtractedNumber, seaIndicator,
      hc, ite_true, hmin, one_smul, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_one, Int.cast_ofNat]
    module
  · have hmin : min (M : ℤ) (k.val - 1) = k.val - 1 := min_eq_right (by omega)
    simp only [seaWickTerm, seaWickWeight, seaSubtractedNumber, seaIndicator,
      hc, ite_false, hmin, zero_smul, sub_zero, Int.cast_add, Int.cast_mul,
      Int.cast_sub, Int.cast_one, Int.cast_ofNat]
    module


theorem raw_inter_eq_hopping (h M : ℕ) (g2 : ℝ)
    (branches : A06.Branches σ) :
    rawInterBranch h M g2 branches =
      hoppingInterBranch h M g2 branches := by
  let f : ℤ → A05.Operators σ h := fun m =>
    seaNormalRho h branches.rightSpecies m * seaNormalRho h branches.leftSpecies (-m)
  have hsum (n : ℕ) :
      (∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f m) =
        f 0 + ∑ m ∈ Finset.Icc 1 n, (f (m : ℤ) + f (-(m : ℤ))) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hi : Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
          insert (-((n + 1 : ℕ) : ℤ))
            (insert ((n + 1 : ℕ) : ℤ) (Finset.Icc (-(n : ℤ)) (n : ℤ))) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
        omega
      have hn : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hp : ((n + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
        simp only [Finset.mem_Icc, Nat.cast_add, Nat.cast_one]
        omega
      have hm : -((n + 1 : ℕ) : ℤ) ∉
          insert ((n + 1 : ℕ) : ℤ) (Finset.Icc (-(n : ℤ)) (n : ℤ)) := by
        simp only [Finset.mem_Icc, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
        omega
      have hnp : n + 1 ∉ Finset.Icc 1 n := by simp
      rw [hi, hn, Finset.sum_insert hm, Finset.sum_insert hp, Finset.sum_insert hnp, ih]
      abel
  unfold rawInterBranch hoppingInterBranch
  dsimp only
  change _ • (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f m) = _
  rw [hsum]
  congr 1
  have hz : f 0 = A05.chargeObservable h branches.rightSpecies *
      A05.chargeObservable h branches.leftSpecies := by
    simp only [f, neg_zero, sea_normal_rho_zero]
  rw [hz]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have hp : (m : ℤ) ≠ 0 := by
    have hh := (Finset.mem_Icc.mp hm).1
    omega
  simp only [f, sea_normal_rho_nonzero h _ _ hp,
    sea_normal_rho_nonzero h _ _ (neg_ne_zero.mpr hp), neg_neg]

lemma hopping_mode_kills_ground (h m : ℕ) (hh : 0 < h) (hm : 1 ≤ m)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (branches : A06.Branches σ) :
    (A05.rho h branches.rightSpecies (m : ℤ) *
        A05.rho h branches.leftSpecies (-(m : ℤ)) +
      A05.rho h branches.rightSpecies (-(m : ℤ)) *
        A05.rho h branches.leftSpecies (m : ℤ))
      (A05.groundKet h Ns) = 0 := by
  have hg := A05.ground_mem_budget h hh Ns hN 0
  have hl (ν : σ) : A05.rho h ν (-(m : ℤ)) (A05.groundKet h Ns) = 0 :=
    A05.rho_lowering_budget_zero h hh ν m 0 (by omega) Ns _ hg
  have hc := A05.rho_cross_commute h branches.rightSpecies branches.leftSpecies
    branches.distinct (-(m : ℤ)) (m : ℤ)
  have he := sub_eq_zero.mp hc
  simp only [LinearMap.add_apply, Module.End.mul_apply, hl, map_zero]
  rw [← Module.End.mul_apply, he, Module.End.mul_apply, hl, map_zero, add_zero]

lemma pairing_mode_ground_nonzero (h M m : ℕ) (hh : 0 < h)
    (hm : 1 ≤ m) (hcut : m ≤ M) (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (branches : A06.Branches σ)
    (hmargin : A06.branchMargins h M m Ns branches) :
    (A05.rho h branches.rightSpecies (m : ℤ) *
        A05.rho h branches.leftSpecies (m : ℤ) +
      A05.rho h branches.rightSpecies (-(m : ℤ)) *
        A05.rho h branches.leftSpecies (-(m : ℤ)))
      (A05.groundKet h Ns) ≠ 0 := by
  have hg := A05.ground_mem_budget h hh Ns hN 0
  have hleft := Ch16.excited_ket_mem_budget h m m hh le_rfl Ns hN branches .left
  have hnz := Ch16.excited_ket_nonzero h M m hh hm hcut Ns hN branches .left hmargin.2
  have hl (ν : σ) : A05.rho h ν (-(m : ℤ)) (A05.groundKet h Ns) = 0 :=
    A05.rho_lowering_budget_zero h hh ν m 0 (by omega) Ns _ hg
  have hcross := sub_eq_zero.mp (A05.rho_cross_commute h branches.rightSpecies
    branches.leftSpecies branches.distinct (-(m : ℤ)) (m : ℤ))
  have hlow : A05.rho h branches.rightSpecies (-(m : ℤ))
      (Ch16.excitedKet h Ns branches .left m) = 0 := by
    unfold Ch16.excitedKet A06.speciesOf
    rw [← Module.End.mul_apply, hcross, Module.End.mul_apply, hl, map_zero]
  have hc := A06.joint_signed_current_commutator h m hh Ns branches.rightSpecies
    (-(m : ℤ)) (m : ℤ) (by
      have hmar := hmargin.1
      unfold A06.marginAt at hmar
      simp only [abs_neg, abs_of_nonneg (Int.natCast_nonneg m)]
      omega) (Ch16.excitedKet h Ns branches .left m) hleft
  simp only [A02.commutator, LinearMap.sub_apply, Module.End.mul_apply, hlow,
    map_zero, sub_zero, Ch10.schwingerCoefficient, neg_add_cancel, ite_true,
    Int.cast_neg, neg_neg] at hc
  intro hz
  simp only [LinearMap.add_apply, Module.End.mul_apply, hl, map_zero, add_zero] at hz
  have hz' := congrArg (A05.rho h branches.rightSpecies (-(m : ℤ))) hz
  change A05.rho h branches.rightSpecies (-(m : ℤ))
    (A05.rho h branches.rightSpecies (m : ℤ) (Ch16.excitedKet h Ns branches .left m)) = _ at hz'
  rw [hc, map_zero] at hz'
  exact (smul_eq_zero.mp hz').elim (by exact_mod_cast (show m ≠ 0 by omega)) hnz

lemma hopping_mode_self_adjoint (h m : ℕ) (v1 v2 : ℝ)
    (branches : A06.Branches σ) :
    LinearMap.adjoint (hoppingMode h m v1 v2 branches) =
      hoppingMode h m v1 v2 branches := by
  have hmul : ∀ X Y : A05.Operators σ h,
      LinearMap.adjoint (X * Y) = LinearMap.adjoint Y * LinearMap.adjoint X := by
    intro X Y
    exact LinearMap.adjoint_comp X Y
  have hρ : ∀ (ν : σ) (n : ℤ),
      LinearMap.adjoint (A05.rho h ν n) = A05.rho h ν (-n) :=
    fun ν n => A05.rho_adjoint h ν n
  have hadj : ∀ (ν η : σ) (a b : ℤ),
      LinearMap.adjoint (A05.rho h ν a * A05.rho h η b) =
        A05.rho h η (-b) * A05.rho h ν (-a) := by
    intro ν η a b
    rw [hmul, hρ, hρ]
  have hs : ∀ x : ℝ, (starRingEnd ℂ) (x : ℂ) = (x : ℂ) := fun x => Complex.conj_ofReal x
  simp only [hoppingMode, map_add, map_smulₛₗ, hadj, hs, neg_neg]
  module

lemma pairing_mode_self_adjoint (h m : ℕ) (v1 v2 : ℝ)
    (branches : A06.Branches σ) :
    LinearMap.adjoint (pairingMode h m v1 v2 branches) =
      pairingMode h m v1 v2 branches := by
  have hmul : ∀ X Y : A05.Operators σ h,
      LinearMap.adjoint (X * Y) = LinearMap.adjoint Y * LinearMap.adjoint X := by
    intro X Y
    exact LinearMap.adjoint_comp X Y
  have hρ : ∀ (ν : σ) (n : ℤ),
      LinearMap.adjoint (A05.rho h ν n) = A05.rho h ν (-n) :=
    fun ν n => A05.rho_adjoint h ν n
  have hadj : ∀ (ν η : σ) (a b : ℤ),
      LinearMap.adjoint (A05.rho h ν a * A05.rho h η b) =
        A05.rho h η (-b) * A05.rho h ν (-a) := by
    intro ν η a b
    rw [hmul, hρ, hρ]
  have hcomm : ∀ a b : ℤ,
      A05.rho h branches.leftSpecies a * A05.rho h branches.rightSpecies b =
        A05.rho h branches.rightSpecies b * A05.rho h branches.leftSpecies a := by
    intro a b
    have hc := A05.rho_cross_commute h branches.rightSpecies branches.leftSpecies
      branches.distinct b a
    unfold A02.commutator at hc
    exact (sub_eq_zero.mp hc).symm
  have hs : ∀ x : ℝ, (starRingEnd ℂ) (x : ℂ) = (x : ℂ) := fun x => Complex.conj_ofReal x
  simp only [pairingMode, map_add, map_smulₛₗ, hadj, hcomm, hs, neg_neg]
  module

lemma bogoliubov_creator_adjoint (h m : ℕ) (c s : ℝ)
    (branches : A06.Branches σ) (η : A06.Orientation) :
    LinearMap.adjoint (bogoliubovCreator h m c s branches η) =
      bogoliubovAnnihilator h m c s branches η := by
  simp only [bogoliubovCreator, bogoliubovAnnihilator, map_add, map_smulₛₗ,
    A05.rho_adjoint, Complex.conj_ofReal, neg_neg]

theorem bogoliubov_expansion_on_budget (h M K m : ℕ) (hh : 0 < h)
    (hm : 1 ≤ m) (hcut : m ≤ M) (v1 v2 : ℝ)
    (hp : HyperbolicParams v1 v2) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    dressedModeNumber h m hp.u hp.c hp.s branches v =
      pairingMode h m v1 v2 branches v +
        ((2 * hp.u * hp.s ^ 2 * (m : ℝ) : ℝ) : ℂ) • v := by
  have _ := hm
  have hCCR (ν : σ) (hb : A06.marginAt h M K Ns ν) :
      A02.commutator (A05.rho h ν (-(m : ℤ))) (A05.rho h ν (m : ℤ)) v = (m : ℂ) • v := by
    have hc := A06.joint_signed_current_commutator h K hh Ns ν
      (-(m : ℤ)) (m : ℤ) (by
        unfold A06.marginAt at hb
        simp only [abs_neg, abs_of_nonneg (Int.natCast_nonneg m)]
        omega) v hv
    simpa only [Ch10.schwingerCoefficient, neg_add_cancel, ite_true,
      Int.cast_neg, neg_neg, Int.cast_natCast] using hc
  have hcomm (p q : ℤ) : A05.rho h branches.leftSpecies p * A05.rho h branches.rightSpecies q =
      A05.rho h branches.rightSpecies q * A05.rho h branches.leftSpecies p :=
    (sub_eq_zero.mp (A05.rho_cross_commute h branches.rightSpecies
      branches.leftSpecies branches.distinct q p)).symm
  have halgebra (u c s : ℂ) (CR AR CL AL : A05.Operators σ h)
      (hCC : CL * CR = CR * CL) (hAA : AL * AR = AR * AL) :
      u • ((c • CR + s • AL) * (c • AR + s • CL) +
        (c • CL + s • AR) * (c • AL + s • CR)) =
      (u * (c^2+s^2)) • (CR*AR+CL*AL) +
      (2*u*c*s) • (CR*CL+AR*AL) +
      (u*s^2) • (A02.commutator AL CL + A02.commutator AR CR) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, A02.commutator]
    rw [hCC, hAA]
    module
  have hid : dressedModeNumber h m hp.u hp.c hp.s branches =
      ((hp.u : ℂ) * ((hp.c : ℂ)^2+(hp.s : ℂ)^2)) •
        (A05.rho h branches.rightSpecies (m : ℤ) * A05.rho h branches.rightSpecies (-(m : ℤ)) +
          A05.rho h branches.leftSpecies (m : ℤ) * A05.rho h branches.leftSpecies (-(m : ℤ))) +
      (2*(hp.u : ℂ)*(hp.c : ℂ)*(hp.s : ℂ)) •
        (A05.rho h branches.rightSpecies (m : ℤ) * A05.rho h branches.leftSpecies (m : ℤ) +
          A05.rho h branches.rightSpecies (-(m : ℤ)) * A05.rho h branches.leftSpecies (-(m : ℤ))) +
      ((hp.u : ℂ)*(hp.s : ℂ)^2) •
        (A02.commutator (A05.rho h branches.leftSpecies (-(m : ℤ))) (A05.rho h branches.leftSpecies (m : ℤ)) +
          A02.commutator (A05.rho h branches.rightSpecies (-(m : ℤ))) (A05.rho h branches.rightSpecies (m : ℤ))) := by
    unfold dressedModeNumber bogoliubovCreator bogoliubovAnnihilator
    simp only [A06.speciesOf, oppositeOrientation]
    exact halgebra _ _ _ _ _ _ _ (hcomm _ _) (hcomm _ _)
  have hv1 : (v1 : ℂ) = (hp.u : ℂ) * ((hp.c : ℂ)^2+(hp.s : ℂ)^2) := by exact_mod_cast hp.match_v1
  have hv2 : (v2 : ℂ) = 2*(hp.u : ℂ)*(hp.c : ℂ)*(hp.s : ℂ) := by exact_mod_cast hp.match_v2
  rw [hid, ← hv1, ← hv2]
  simp only [LinearMap.add_apply, LinearMap.smul_apply,
    hCCR branches.leftSpecies hmargin.2, hCCR branches.rightSpecies hmargin.1]
  simp only [pairingMode, LinearMap.add_apply, LinearMap.smul_apply,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_natCast]
  module

theorem bogoliubov_ccr_on_budget (h M K m : ℕ) (hh : 0 < h)
    (hm : 1 ≤ m) (hcut : m ≤ M) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1)
    (branches : A06.Branches σ) (η : A06.Orientation)
    (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator
        (bogoliubovAnnihilator h m c s branches η)
        (bogoliubovCreator h m c s branches η) v =
      (m : ℂ) • v := by
  have _ := hm
  have hmar (θ : A06.Orientation) : A06.marginAt h M K Ns (A06.speciesOf branches θ) := by
    cases θ
    · exact hmargin.1
    · exact hmargin.2
  have hCCR (θ : A06.Orientation) :
      A02.commutator (A05.rho h (A06.speciesOf branches θ) (-(m : ℤ)))
        (A05.rho h (A06.speciesOf branches θ) (m : ℤ)) v = (m : ℂ) • v := by
    have hc := A06.joint_signed_current_commutator h K hh Ns (A06.speciesOf branches θ)
      (-(m : ℤ)) (m : ℤ) (by
        have hb := hmar θ
        unfold A06.marginAt at hb
        simp only [abs_neg, abs_of_nonneg (Int.natCast_nonneg m)]
        omega) v hv
    simpa only [Ch10.schwingerCoefficient, neg_add_cancel, ite_true,
      Int.cast_neg, neg_neg, Int.cast_natCast] using hc
  have hdistinct : A06.speciesOf branches η ≠ A06.speciesOf branches (oppositeOrientation η) := by
    cases η
    · exact branches.distinct
    · exact branches.distinct.symm
  have hcross (p q : ℤ) := A05.rho_cross_commute h (A06.speciesOf branches η)
    (A06.speciesOf branches (oppositeOrientation η)) hdistinct p q
  have hbilin (a b : ℂ) (A B C D : A05.Operators σ h) :
      A02.commutator (a • A + b • B) (a • C + b • D) =
      (a*a) • A02.commutator A C + (a*b) • A02.commutator A D +
      (b*a) • A02.commutator B C + (b*b) • A02.commutator B D := by
    simp only [A02.commutator, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      smul_sub]
    module
  have hreverse (A B : A05.Operators σ h) : A02.commutator B A = -A02.commutator A B := by
    simp only [A02.commutator]
    abel
  unfold bogoliubovAnnihilator bogoliubovCreator
  rw [hbilin, hcross,
    hreverse (A05.rho h (A06.speciesOf branches η) (m : ℤ))
      (A05.rho h (A06.speciesOf branches (oppositeOrientation η)) (m : ℤ)),
    hcross,
    hreverse (A05.rho h (A06.speciesOf branches (oppositeOrientation η)) (-(m : ℤ)))
      (A05.rho h (A06.speciesOf branches (oppositeOrientation η)) (m : ℤ))]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    LinearMap.zero_apply, hCCR, neg_zero]
  have hcs' : (c : ℂ)^2 - (s : ℂ)^2 = 1 := by exact_mod_cast hcs
  calc
    _ = (((c : ℂ)^2 - (s : ℂ)^2) * (m : ℂ)) • v := by module
    _ = (m : ℂ) • v := by rw [hcs', one_mul]

end Operators

end Bosonize.A07Interactions
