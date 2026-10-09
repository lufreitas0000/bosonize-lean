module

public import Bosonize.Core.A01FourierCharacters
public import Bosonize.Core.Ch03Fourier
public import Bosonize.Core.Ch04CARFock

/-!
# Chapter 5: position and momentum fermions
Phase A: complete definitions and one-sorry review stubs.
The Fourier layer works for positive L; physical sea formulas specialize to L = 2*h, h > 0.
-/

@[expose] public section

namespace Bosonize.Ch05

open scoped BigOperators

abbrev FockSpace (L : ℕ) := A02.FockSpace (Ch01.Band L)
abbrev Operators (L : ℕ) := Module.End ℂ (FockSpace L)

noncomputable def momentumAnnihilation (L : ℕ) (k : Ch01.Band L) : Operators L :=
  Ch04.annihilation k

noncomputable def momentumCreation (L : ℕ) (k : Ch01.Band L) : Operators L :=
  Ch04.creation k

noncomputable def momentumNumber (L : ℕ) (k : Ch01.Band L) : Operators L :=
  momentumCreation L k * momentumAnnihilation L k

/-- Positive character kernel for annihilators, with the real unitary normalization. -/
noncomputable def positionAnnihilation (L : ℕ) [NeZero L]
    (x : Ch01.Lattice L) : Operators L :=
  (A01.normalization L : ℂ) • ∑ k : Ch01.Band L,
    A01.bandCharacter L (A01.canonicalRoot L) k x • momentumAnnihilation L k

/-- Ordinary integer negation in the character; no negative-band membership is assumed. -/
noncomputable def positionCreation (L : ℕ) [NeZero L]
    (x : Ch01.Lattice L) : Operators L :=
  (A01.normalization L : ℂ) • ∑ k : Ch01.Band L,
    A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) • momentumCreation L k

noncomputable def positionNumber (L : ℕ) [NeZero L]
    (x : Ch01.Lattice L) : Operators L :=
  positionCreation L x * positionAnnihilation L x

noncomputable def totalNumber (L : ℕ) : Operators L :=
  ∑ k : Ch01.Band L, momentumNumber L k

/-- Integer spectrum, without clipping negative bare energies. -/
def occupationEnergy (L : ℕ) (S : A02.Occupation (Ch01.Band L)) : ℤ :=
  ∑ k ∈ S, k.val

noncomputable def bareHamiltonian (L : ℕ) : Operators L :=
  ∑ k : Ch01.Band L, (k.val : ℂ) • momentumNumber L k

/-- Fill all nonpositive labels in the actual positive-Nyquist band. -/
def seaConfiguration (L : ℕ) : A02.Occupation (Ch01.Band L) :=
  Finset.univ.filter (fun k => k.val ≤ 0)

def seaEnergy (L : ℕ) : ℤ := occupationEnergy L (seaConfiguration L)

noncomputable def seaKet (L : ℕ) : FockSpace L := A02.ket (seaConfiguration L)

noncomputable def shiftedHamiltonian (L : ℕ) : Operators L :=
  bareHamiltonian L - (seaEnergy L : ℂ) • (1 : Operators L)

noncomputable def parity (L : ℕ) : Operators L := Ch04.parity

section Fourier
variable (L : ℕ) [NeZero L]

lemma position_creation_eq_adjoint (x : Ch01.Lattice L) :
    positionCreation L x = LinearMap.adjoint (positionAnnihilation L x) := by sorry

lemma position_annihilation_eq_adjoint (x : Ch01.Lattice L) :
    positionAnnihilation L x = LinearMap.adjoint (positionCreation L x) := by sorry

lemma position_annihilation_car (x y : Ch01.Lattice L) :
    A02.anticommutator (positionAnnihilation L x) (positionAnnihilation L y) = 0 := by sorry

lemma position_creation_car (x y : Ch01.Lattice L) :
    A02.anticommutator (positionCreation L x) (positionCreation L y) = 0 := by sorry

lemma position_mixed_car (x y : Ch01.Lattice L) :
    A02.anticommutator (positionAnnihilation L x) (positionCreation L y) =
      (if x = y then (1 : ℂ) else 0) • (1 : Operators L) := by sorry

lemma position_car_exists : ∃ R : A02.CAR (Ch01.Lattice L) (FockSpace L),
    R.annihilation = positionAnnihilation L ∧ R.creation = positionCreation L := by sorry

lemma inverse_annihilation (k : Ch01.Band L) :
    momentumAnnihilation L k = (A01.normalization L : ℂ) •
      ∑ x : Ch01.Lattice L,
        A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) •
          positionAnnihilation L x := by sorry

lemma inverse_creation (k : Ch01.Band L) :
    momentumCreation L k = (A01.normalization L : ℂ) •
      ∑ x : Ch01.Lattice L,
        A01.bandCharacter L (A01.canonicalRoot L) k x • positionCreation L x := by sorry

lemma total_number_position :
    (∑ x : Ch01.Lattice L, positionNumber L x) = totalNumber L := by sorry

lemma position_number_idempotent (x : Ch01.Lattice L) :
    positionNumber L x * positionNumber L x = positionNumber L x := by sorry

lemma position_number_adjoint (x : Ch01.Lattice L) :
    LinearMap.adjoint (positionNumber L x) = positionNumber L x := by sorry

lemma position_number_commute (x y : Ch01.Lattice L) :
    positionNumber L x * positionNumber L y = positionNumber L y * positionNumber L x := by sorry

lemma position_annihilation_vacuum (x : Ch01.Lattice L) :
    positionAnnihilation L x (A02.ket ∅) = 0 := by sorry

lemma position_creation_vacuum_ne_zero (x : Ch01.Lattice L) :
    positionCreation L x (A02.ket ∅) ≠ 0 := by sorry

lemma parity_position_creation (x : Ch01.Lattice L) :
    parity L * positionCreation L x = -(positionCreation L x * parity L) := by sorry

lemma parity_position_annihilation (x : Ch01.Lattice L) :
    parity L * positionAnnihilation L x = -(positionAnnihilation L x * parity L) := by sorry

lemma total_number_position_creation_commutator (x : Ch01.Lattice L) :
    A02.commutator (totalNumber L) (positionCreation L x) = positionCreation L x := by sorry

lemma total_number_position_annihilation_commutator (x : Ch01.Lattice L) :
    A02.commutator (totalNumber L) (positionAnnihilation L x) = -positionAnnihilation L x := by sorry

end Fourier

section Energy
variable (L : ℕ)

lemma total_number_ket (S : A02.Occupation (Ch01.Band L)) :
    totalNumber L (A02.ket S) = (S.card : ℂ) • A02.ket S := by sorry

lemma bare_hamiltonian_ket (S : A02.Occupation (Ch01.Band L)) :
    bareHamiltonian L (A02.ket S) = (occupationEnergy L S : ℂ) • A02.ket S := by sorry

lemma shifted_hamiltonian_ket (S : A02.Occupation (Ch01.Band L)) :
    shiftedHamiltonian L (A02.ket S) =
      ((occupationEnergy L S - seaEnergy L : ℤ) : ℂ) • A02.ket S := by sorry

lemma bare_hamiltonian_adjoint :
    LinearMap.adjoint (bareHamiltonian L) = bareHamiltonian L := by sorry

lemma shifted_hamiltonian_adjoint :
    LinearMap.adjoint (shiftedHamiltonian L) = shiftedHamiltonian L := by sorry

lemma bare_creation_commutator (k : Ch01.Band L) :
    A02.commutator (bareHamiltonian L) (momentumCreation L k) =
      (k.val : ℂ) • momentumCreation L k := by sorry

lemma bare_annihilation_commutator (k : Ch01.Band L) :
    A02.commutator (bareHamiltonian L) (momentumAnnihilation L k) =
      (-k.val : ℂ) • momentumAnnihilation L k := by sorry

lemma shifted_creation_commutator (k : Ch01.Band L) :
    A02.commutator (shiftedHamiltonian L) (momentumCreation L k) =
      (k.val : ℂ) • momentumCreation L k := by sorry

lemma shifted_annihilation_commutator (k : Ch01.Band L) :
    A02.commutator (shiftedHamiltonian L) (momentumAnnihilation L k) =
      (-k.val : ℂ) • momentumAnnihilation L k := by sorry

lemma sea_ket_ne_zero : seaKet L ≠ 0 := by sorry

lemma bare_hamiltonian_sea :
    bareHamiltonian L (seaKet L) = (seaEnergy L : ℂ) • seaKet L := by sorry

lemma shifted_hamiltonian_sea : shiftedHamiltonian L (seaKet L) = 0 := by sorry

end Energy

/-- These physical contracts use exactly the notes' positive-even lattice. -/
lemma sea_card_even (h : ℕ) (hh : 0 < h) : (seaConfiguration (2*h)).card = h := by sorry

lemma sea_energy_even (h : ℕ) (hh : 0 < h) :
    seaEnergy (2*h) = -((h : ℤ) * ((h : ℤ) - 1) / 2) := by sorry

lemma sea_energy_negative (h : ℕ) (hh : 2 ≤ h) : seaEnergy (2*h) < 0 := by sorry

lemma bare_sea_action_ne_zero (h : ℕ) (hh : 2 ≤ h) :
    bareHamiltonian (2*h) (seaKet (2*h)) ≠ 0 := by sorry

lemma sea_energy_half_size_one : seaEnergy 2 = 0 := by sorry

end Bosonize.Ch05
