import Bosonize.Core.Ch14Mandelstam
import Bosonize.Core.Ch16FieldHamiltonian
import Bosonize.Core.Ch17LuttingerModels
import Bosonize.Core.Ch18Bogoliubov
import Mathlib.Analysis.Real.Pi.Bounds

namespace Bosonize.Ch20ResidualScratch
open scoped BigOperators Classical
variable {σ : Type*} [Fintype σ] [LinearOrder σ]
noncomputable local instance modeOrd (h : ℕ) : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
noncomputable local instance modeDecEq (h : ℕ) : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq

lemma creatorKet (h : ℕ) (ν : σ) (k : Ch01.Band (2*h)) (S : A05.Occupation σ h) :
  LinearMap.adjoint (A05.annihilation h ν k) (A02.ket S) =
  if (ν,k) ∉ S then Ch04.fermionSign (ν,k) S • A02.ket (insert (ν,k) S) else 0 := by
  simp [A05.annihilation, Ch04.annihilation_eq_adjoint, LinearMap.adjoint_adjoint, Ch04.creation_ket]

lemma adjointLiftedKet (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (ν : σ) (x : ℤ) (S : A05.Occupation σ h) :
    LinearMap.adjoint (A05.liftedAnnihilation h b ν x) (A02.ket S) =
      star (A01.normalization (2*h) : ℂ) •
       ∑ k : Ch01.Band (2*h),
        star (Ch06Ext.twistedCharacter (2*h) (b ν) k x) •
          (if (ν,k) ∉ S then Ch04.fermionSign (ν,k) S • A02.ket (insert (ν,k) S) else 0) := by
  rw [← LinearMap.star_eq_adjoint]
  simp [A05.liftedAnnihilation, A05.annihilation, Ch04.annihilation_eq_adjoint,
    LinearMap.star_eq_adjoint, LinearMap.adjoint_adjoint, Ch04.creation_ket]

end Bosonize.Ch20ResidualScratch
