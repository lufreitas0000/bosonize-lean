module

public import Bosonize.Core.Ch01LatticeBand
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Appendix A01: Fourier characters and normalization

Phase C: definitions and all lemmas are proved, audited, and frozen in Core.
Generic orthogonality uses a field, and division by L has a separate scalar hypothesis.
-/

@[expose] public section

namespace Bosonize.A01

open scoped BigOperators

variable {K : Type*} [Field K]

/-- The integer pairing, including ordinary negative momentum labels. -/
def integerCharacter (ζ : K) (k x : ℤ) : K := ζ ^ (k * x)

/-- Evaluate the integer pairing on the standard residue representatives. -/
def residueCharacter (L : ℕ) (ζ : K) (k x : Ch01.Lattice L) : K :=
  integerCharacter ζ (k.val : ℤ) (x.val : ℤ)

/-- Signed band evaluation; integer negation need not remain in the band. -/
def bandCharacter (L : ℕ) (ζ : K) (k : Ch01.Band L) (x : Ch01.Lattice L) : K :=
  integerCharacter ζ k.val (x.val : ℤ)

/-- The existing positive-Nyquist band equivalence, using only frozen Core proofs. -/
noncomputable def bandEquiv (L : ℕ) [NeZero L] : Ch01.Band L ≃ Ch01.Lattice L :=
  Equiv.ofBijective (Ch01.bandProjection L)
    (Ch01.band_projection_bijective L (Nat.pos_of_ne_zero (NeZero.ne L)))

/-- The canonical root for the physical complex layer. -/
noncomputable def canonicalRoot (L : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (L : ℂ))

/-- The one real normalization scalar; claims below exclude L = 0. -/
noncomputable def normalization (L : ℕ) : ℝ := (Real.sqrt (L : ℝ))⁻¹

lemma root_pow_size (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) :
    ζ ^ L = 1 := by
  exact hζ.pow_eq_one

lemma root_ne_zero (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) :
    ζ ≠ 0 := by
  exact hζ.ne_zero (NeZero.ne L)

lemma character_representative_independent (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x s t : ℤ) :
    integerCharacter ζ (k + s * (L : ℤ)) (x + t * (L : ℤ)) =
      integerCharacter ζ k x := by
  have hn := root_ne_zero L ζ hζ
  have hp : ζ ^ (L : ℤ) = 1 := by simpa using hζ.pow_eq_one
  unfold integerCharacter
  have he : (k + s * (L : ℤ)) * (x + t * (L : ℤ)) =
      k * x + (L : ℤ) * (k * t + s * x + s * t * (L : ℤ)) := by ring
  rw [he, zpow_add₀ hn, zpow_mul ζ (L : ℤ), hp, one_zpow, mul_one]

lemma residue_character_int_cast (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) :
    residueCharacter L ζ (k : Ch01.Lattice L) (x : Ch01.Lattice L) =
      integerCharacter ζ k x := by
  unfold residueCharacter
  rw [ZMod.val_intCast, ZMod.val_intCast]
  have he (a : ℤ) : a % (L : ℤ) = a + (-(a / (L : ℤ))) * (L : ℤ) := by
    have h := Int.emod_add_mul_ediv a (L : ℤ)
    nlinarith
  rw [he k, he x]
  exact character_representative_independent L ζ hζ k x _ _

lemma residue_character_add_right (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x y : Ch01.Lattice L) :
    residueCharacter L ζ k (x + y) =
      residueCharacter L ζ k x * residueCharacter L ζ k y := by
  have hc (r : Ch01.Lattice L) : ((r.val : ℤ) : Ch01.Lattice L) = r := by
    simp
  rw [← hc k, ← hc x, ← hc y, ← Int.cast_add]
  simp only [residue_character_int_cast L ζ hζ, integerCharacter, mul_add,
    zpow_add₀ (root_ne_zero L ζ hζ)]

lemma residue_character_add_left (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p x : Ch01.Lattice L) :
    residueCharacter L ζ (k + p) x =
      residueCharacter L ζ k x * residueCharacter L ζ p x := by
  have hc (r : Ch01.Lattice L) : ((r.val : ℤ) : Ch01.Lattice L) = r := by
    simp
  rw [← hc k, ← hc p, ← hc x, ← Int.cast_add]
  simp only [residue_character_int_cast L ζ hζ, integerCharacter, add_mul,
    zpow_add₀ (root_ne_zero L ζ hζ)]

lemma residue_character_zero (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (x : Ch01.Lattice L) :
    residueCharacter L ζ 0 x = 1 := by
  cases hζ
  simp [residueCharacter, integerCharacter]

lemma residue_character_neg (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x : Ch01.Lattice L) :
    residueCharacter L ζ (-k) x = (residueCharacter L ζ k x)⁻¹ := by
  have hc (r : Ch01.Lattice L) : ((r.val : ℤ) : Ch01.Lattice L) = r := by simp
  calc
    residueCharacter L ζ (-k) x = integerCharacter ζ (-(k.val : ℤ)) (x.val : ℤ) := by
      simpa only [Int.cast_neg, hc] using residue_character_int_cast L ζ hζ (-(k.val : ℤ)) (x.val : ℤ)
    _ = (residueCharacter L ζ k x)⁻¹ := by
      rw [show residueCharacter L ζ k x = integerCharacter ζ (k.val : ℤ) (x.val : ℤ) from
        by simpa only [hc] using residue_character_int_cast L ζ hζ (k.val : ℤ) (x.val : ℤ)]
      simp [integerCharacter]

lemma residue_character_sub (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p x : Ch01.Lattice L) :
    residueCharacter L ζ (k - p) x =
      residueCharacter L ζ k x * (residueCharacter L ζ p x)⁻¹ := by
  rw [sub_eq_add_neg, residue_character_add_left L ζ hζ,
    residue_character_neg L ζ hζ]

lemma character_ne_zero (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) : integerCharacter ζ k x ≠ 0 := by
  exact zpow_ne_zero _ (root_ne_zero L ζ hζ)

lemma character_nontrivial (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Lattice L) (hk : k ≠ 0) :
    ∃ x : Ch01.Lattice L, residueCharacter L ζ k x ≠ 1 := by
  classical
  have he : (L : ℤ) ∣ (k.val : ℤ) → False := by
    intro hd
    apply hk
    have hz : (k.val : ℤ) = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt
      (by positivity) (by exact_mod_cast ZMod.val_lt k) hd
    simpa using congrArg (fun a : ℤ ↦ (a : Ch01.Lattice L)) hz
  refine ⟨1, ?_⟩
  have hc : ((k.val : ℤ) : Ch01.Lattice L) = k := by simp
  have hr : residueCharacter L ζ k 1 = ζ ^ (k.val : ℤ) := by
    simpa only [hc, Int.cast_one, integerCharacter, mul_one] using
      residue_character_int_cast L ζ hζ (k.val : ℤ) 1
  rw [hr]
  intro h
  have hu := hζ.isUnit (NeZero.ne L)
  have hp : (hu.unit : Kˣ) ^ (k.val : ℤ) = 1 := by
    apply Units.val_injective
    simpa using h
  have hprim : IsPrimitiveRoot hu.unit L := by
    exact (IsPrimitiveRoot.coe_units_iff).mp (by simpa using hζ)
  exact he ((hprim.zpow_eq_one_iff_dvd _).mp hp)

lemma band_character_projection (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) (x : Ch01.Lattice L) :
    bandCharacter L ζ k x = residueCharacter L ζ (Ch01.bandProjection L k) x := by
  have hc : ((x.val : ℤ) : Ch01.Lattice L) = x := by simp
  simpa only [hc, bandCharacter, Ch01.bandProjection, Ch01.quotientMap] using
    (residue_character_int_cast L ζ hζ k.val (x.val : ℤ)).symm

lemma band_character_add (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p : Ch01.Band L) (x : Ch01.Lattice L) :
    bandCharacter L ζ (Ch01.bandAdd L (Nat.pos_of_ne_zero (NeZero.ne L)) k p) x =
      bandCharacter L ζ k x * bandCharacter L ζ p x := by
  rw [band_character_projection L ζ hζ, Ch01.band_add_projection,
    residue_character_add_left L ζ hζ, ← band_character_projection L ζ hζ,
    ← band_character_projection L ζ hζ]

lemma band_character_neg (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) (x : Ch01.Lattice L) :
    bandCharacter L ζ (Ch01.bandNeg L (Nat.pos_of_ne_zero (NeZero.ne L)) k) x =
      integerCharacter ζ (-k.val) (x.val : ℤ) := by
  rw [band_character_projection L ζ hζ, Ch01.band_neg_projection]
  change residueCharacter L ζ (-(k.val : Ch01.Lattice L)) x = _
  rw [← ZMod.natCast_zmod_val x, ← Int.cast_neg]
  simpa using residue_character_int_cast L ζ hζ (-k.val) (x.val : ℤ)

lemma band_character_sub (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p : Ch01.Band L) (x : Ch01.Lattice L) :
    bandCharacter L ζ
      (Ch01.bandAdd L (Nat.pos_of_ne_zero (NeZero.ne L)) k
        (Ch01.bandNeg L (Nat.pos_of_ne_zero (NeZero.ne L)) p)) x =
      integerCharacter ζ (k.val - p.val) (x.val : ℤ) := by
  rw [band_character_projection L ζ hζ, Ch01.band_add_projection,
    Ch01.band_neg_projection]
  change residueCharacter L ζ ((k.val : Ch01.Lattice L) + -(p.val : Ch01.Lattice L)) x = _
  rw [← Int.cast_neg, ← Int.cast_add, ← ZMod.natCast_zmod_val x]
  simpa [sub_eq_add_neg] using residue_character_int_cast L ζ hζ (k.val - p.val) (x.val : ℤ)

lemma sum_band_eq_sum_lattice (L : ℕ) [NeZero L] (f : Ch01.Lattice L → K) :
    (∑ k : Ch01.Band L, f (Ch01.bandProjection L k)) = ∑ x : Ch01.Lattice L, f x := by
  exact (bandEquiv L).sum_comp f

lemma character_sum (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Lattice L) :
    (∑ x : Ch01.Lattice L, residueCharacter L ζ k x) =
      if k = 0 then (L : K) else 0 := by
  classical
  by_cases hk : k = 0
  · simp [hk, residue_character_zero L ζ hζ, ZMod.card]
  · let ψ : AddChar (Ch01.Lattice L) K :=
      { toFun := residueCharacter L ζ k
        map_zero_eq_one' := by simp [residueCharacter, integerCharacter]
        map_add_eq_mul' := residue_character_add_right L ζ hζ k }
    have hψ : ψ ≠ 1 := by
      obtain ⟨x, hx⟩ := character_nontrivial L ζ hζ k hk
      intro he
      exact hx (congrArg (fun c : AddChar (Ch01.Lattice L) K ↦ c x) he)
    change (∑ x, ψ x) = _
    rw [ite_eq_right hk]
    exact AddChar.sum_eq_zero_of_ne_one hψ

lemma character_orthogonality (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p : Ch01.Band L) :
    (∑ x : Ch01.Lattice L, integerCharacter ζ (k.val - p.val) (x.val : ℤ)) =
      if k = p then (L : K) else 0 := by
  classical
  have hc (r : Ch01.Lattice L) : ((r.val : ℤ) : Ch01.Lattice L) = r := by simp
  have he (x : Ch01.Lattice L) : integerCharacter ζ (k.val - p.val) (x.val : ℤ) =
      residueCharacter L ζ (Ch01.bandProjection L k - Ch01.bandProjection L p) x := by
    simpa only [Int.cast_sub, hc, Ch01.bandProjection, Ch01.quotientMap] using
      (residue_character_int_cast L ζ hζ (k.val - p.val) (x.val : ℤ)).symm
  simp_rw [he]
  rw [character_sum L ζ hζ]
  have hi : Ch01.bandProjection L k - Ch01.bandProjection L p = 0 ↔ k = p :=
    sub_eq_zero.trans (Ch01.band_projection_bijective L
      (Nat.pos_of_ne_zero (NeZero.ne L))).injective.eq_iff
  simp only [hi]

lemma dual_character_orthogonality (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (x y : Ch01.Lattice L) :
    (∑ k : Ch01.Band L, integerCharacter ζ k.val ((x.val : ℤ) - (y.val : ℤ))) =
      if x = y then (L : K) else 0 := by
  classical
  have hc (r : Ch01.Lattice L) : ((r.val : ℤ) : Ch01.Lattice L) = r := by simp
  have he (k : Ch01.Band L) : integerCharacter ζ k.val ((x.val : ℤ) - (y.val : ℤ)) =
      residueCharacter L ζ (x - y) (Ch01.bandProjection L k) := by
    have h := residue_character_int_cast L ζ hζ ((x.val : ℤ) - (y.val : ℤ)) k.val
    simpa only [Int.cast_sub, hc, Ch01.bandProjection, Ch01.quotientMap,
      integerCharacter, mul_comm] using h.symm
  simp_rw [he]
  rw [sum_band_eq_sum_lattice, character_sum L ζ hζ]
  simp only [sub_eq_zero]

lemma canonical_root_primitive (L : ℕ) [NeZero L] :
    IsPrimitiveRoot (canonicalRoot L) L := by
  exact Complex.isPrimitiveRoot_exp L (NeZero.ne L)

lemma canonical_character_std (L : ℕ) [NeZero L] (k x : Ch01.Lattice L) :
    residueCharacter L (canonicalRoot L) k x = ZMod.stdAddChar (k * x) := by
  have hc (r : Ch01.Lattice L) : ((r.val : ℤ) : Ch01.Lattice L) = r := by simp
  rw [← hc k, ← hc x, residue_character_int_cast L (canonicalRoot L)
    (canonical_root_primitive L), ← Int.cast_mul, ZMod.stdAddChar_coe]
  unfold integerCharacter canonicalRoot
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

lemma complex_character_conj (L : ℕ) [NeZero L] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) :
    star (integerCharacter ζ k x) = integerCharacter ζ (-k) x := by
  have hn : ‖integerCharacter ζ k x‖ = 1 := by
    unfold integerCharacter
    rw [norm_zpow, hζ.norm'_eq_one (NeZero.ne L), one_zpow]
  have hi : star (integerCharacter ζ k x) = (integerCharacter ζ k x)⁻¹ :=
    (Complex.inv_eq_conj hn).symm
  rw [hi]
  simp [integerCharacter]

lemma complex_character_norm (L : ℕ) [NeZero L] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) : ‖integerCharacter ζ k x‖ = 1 := by
  unfold integerCharacter
  rw [norm_zpow, hζ.norm'_eq_one (NeZero.ne L), one_zpow]

lemma normalization_pos (L : ℕ) [NeZero L] : 0 < normalization L := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)))

lemma normalization_square (L : ℕ) [NeZero L] :
    (L : ℝ) * normalization L ^ 2 = 1 := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold normalization
  rw [inv_pow, Real.sq_sqrt hL.le]
  exact mul_inv_cancel₀ hL.ne'

lemma normalization_conj (L : ℕ) :
    star (normalization L : ℂ) = (normalization L : ℂ) := by
  simp

lemma normalization_square_complex (L : ℕ) [NeZero L] :
    (L : ℂ) * (normalization L : ℂ) ^ 2 = 1 := by
  exact_mod_cast normalization_square L

/-- Scalar contract needed by later position CAR, without asserting a CAR model here. -/
lemma normalization_car_coefficient (L : ℕ) [NeZero L] :
    ‖(normalization L : ℂ)‖ ^ 2 * (L : ℝ) = 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (normalization_pos L)]
  nlinarith [normalization_square L]

lemma singleton_character (ζ : K) (hζ : IsPrimitiveRoot ζ 1)
    (k : Ch01.Band 1) (x : Ch01.Lattice 1) : bandCharacter 1 ζ k x = 1 := by
  cases hζ
  simp [bandCharacter, integerCharacter, Ch01.singleton_band k]

lemma nyquist_character_neg (L : ℕ) [NeZero L] (hEven : Even L)
    (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L)
    (hk : k.val = ((L / 2 : ℕ) : ℤ)) (x : Ch01.Lattice L) :
    integerCharacter ζ (-k.val) (x.val : ℤ) = bandCharacter L ζ k x := by
  rw [← band_character_neg L ζ hζ,
    Ch01.nyquist_neg L (Nat.pos_of_ne_zero (NeZero.ne L)) hEven k hk]

end Bosonize.A01
