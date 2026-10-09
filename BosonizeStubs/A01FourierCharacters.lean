module

public import Bosonize.Core.Ch01LatticeBand
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Appendix A01: Fourier characters and normalization

Phase A, unlocked: definitions are complete; every lemma is an unproved review stub.
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
    ζ ^ L = 1 := by sorry

lemma root_ne_zero (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) :
    ζ ≠ 0 := by sorry

lemma character_representative_independent (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x s t : ℤ) :
    integerCharacter ζ (k + s * (L : ℤ)) (x + t * (L : ℤ)) =
      integerCharacter ζ k x := by sorry

lemma residue_character_int_cast (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) :
    residueCharacter L ζ (k : Ch01.Lattice L) (x : Ch01.Lattice L) =
      integerCharacter ζ k x := by sorry

lemma residue_character_add_right (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x y : Ch01.Lattice L) :
    residueCharacter L ζ k (x + y) =
      residueCharacter L ζ k x * residueCharacter L ζ k y := by sorry

lemma residue_character_add_left (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p x : Ch01.Lattice L) :
    residueCharacter L ζ (k + p) x =
      residueCharacter L ζ k x * residueCharacter L ζ p x := by sorry

lemma residue_character_zero (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (x : Ch01.Lattice L) :
    residueCharacter L ζ 0 x = 1 := by sorry

lemma residue_character_neg (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x : Ch01.Lattice L) :
    residueCharacter L ζ (-k) x = (residueCharacter L ζ k x)⁻¹ := by sorry

lemma residue_character_sub (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p x : Ch01.Lattice L) :
    residueCharacter L ζ (k - p) x =
      residueCharacter L ζ k x * (residueCharacter L ζ p x)⁻¹ := by sorry

lemma character_ne_zero (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) : integerCharacter ζ k x ≠ 0 := by sorry

lemma character_nontrivial (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Lattice L) (hk : k ≠ 0) :
    ∃ x : Ch01.Lattice L, residueCharacter L ζ k x ≠ 1 := by sorry

lemma band_character_projection (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) (x : Ch01.Lattice L) :
    bandCharacter L ζ k x = residueCharacter L ζ (Ch01.bandProjection L k) x := by sorry

lemma band_character_add (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p : Ch01.Band L) (x : Ch01.Lattice L) :
    bandCharacter L ζ (Ch01.bandAdd L (Nat.pos_of_ne_zero (NeZero.ne L)) k p) x =
      bandCharacter L ζ k x * bandCharacter L ζ p x := by sorry

lemma band_character_neg (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) (x : Ch01.Lattice L) :
    bandCharacter L ζ (Ch01.bandNeg L (Nat.pos_of_ne_zero (NeZero.ne L)) k) x =
      integerCharacter ζ (-k.val) (x.val : ℤ) := by sorry

lemma band_character_sub (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p : Ch01.Band L) (x : Ch01.Lattice L) :
    bandCharacter L ζ
      (Ch01.bandAdd L (Nat.pos_of_ne_zero (NeZero.ne L)) k
        (Ch01.bandNeg L (Nat.pos_of_ne_zero (NeZero.ne L)) p)) x =
      integerCharacter ζ (k.val - p.val) (x.val : ℤ) := by sorry

lemma sum_band_eq_sum_lattice (L : ℕ) [NeZero L] (f : Ch01.Lattice L → K) :
    (∑ k : Ch01.Band L, f (Ch01.bandProjection L k)) = ∑ x : Ch01.Lattice L, f x := by sorry

lemma character_sum (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Lattice L) :
    (∑ x : Ch01.Lattice L, residueCharacter L ζ k x) =
      if k = 0 then (L : K) else 0 := by sorry

lemma character_orthogonality (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p : Ch01.Band L) :
    (∑ x : Ch01.Lattice L, integerCharacter ζ (k.val - p.val) (x.val : ℤ)) =
      if k = p then (L : K) else 0 := by sorry

lemma dual_character_orthogonality (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (x y : Ch01.Lattice L) :
    (∑ k : Ch01.Band L, integerCharacter ζ k.val ((x.val : ℤ) - (y.val : ℤ))) =
      if x = y then (L : K) else 0 := by sorry

lemma canonical_root_primitive (L : ℕ) [NeZero L] :
    IsPrimitiveRoot (canonicalRoot L) L := by sorry

lemma canonical_character_std (L : ℕ) [NeZero L] (k x : Ch01.Lattice L) :
    residueCharacter L (canonicalRoot L) k x = ZMod.stdAddChar (k * x) := by sorry

lemma complex_character_conj (L : ℕ) [NeZero L] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) :
    star (integerCharacter ζ k x) = integerCharacter ζ (-k) x := by sorry

lemma complex_character_norm (L : ℕ) [NeZero L] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) : ‖integerCharacter ζ k x‖ = 1 := by sorry

lemma normalization_pos (L : ℕ) [NeZero L] : 0 < normalization L := by sorry

lemma normalization_square (L : ℕ) [NeZero L] :
    (L : ℝ) * normalization L ^ 2 = 1 := by sorry

lemma normalization_conj (L : ℕ) :
    star (normalization L : ℂ) = (normalization L : ℂ) := by sorry

lemma normalization_square_complex (L : ℕ) [NeZero L] :
    (L : ℂ) * (normalization L : ℂ) ^ 2 = 1 := by sorry

/-- Scalar contract needed by later position CAR, without asserting a CAR model here. -/
lemma normalization_car_coefficient (L : ℕ) [NeZero L] :
    ‖(normalization L : ℂ)‖ ^ 2 * (L : ℝ) = 1 := by sorry

lemma singleton_character (ζ : K) (hζ : IsPrimitiveRoot ζ 1)
    (k : Ch01.Band 1) (x : Ch01.Lattice 1) : bandCharacter 1 ζ k x = 1 := by sorry

lemma nyquist_character_neg (L : ℕ) [NeZero L] (hEven : Even L)
    (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L)
    (hk : k.val = ((L / 2 : ℕ) : ℤ)) (x : Ch01.Lattice L) :
    integerCharacter ζ (-k.val) (x.val : ℤ) = bandCharacter L ζ k x := by sorry

end Bosonize.A01
