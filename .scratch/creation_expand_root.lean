import BosonizeStubs.Ch20CDW
namespace Bosonize.Ch20
open scoped BigOperators Classical
variable {σ : Type*} [Fintype σ] [LinearOrder σ]
noncomputable local instance localModeLinearOrder (h : ℕ) : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
noncomputable local instance localModeDecidableEq (h : ℕ) : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq
example (h : ℕ) (b : Fin 2 → Ch06Ext.BoundaryTwist (2*h))
    (ν : Fin 2) (x : ℤ) (S : A05.Occupation (Fin 2) h) :
    (LinearMap.adjoint (A05.liftedAnnihilation h b ν x)) (A02.ket S) =
      star (A01.normalization (2*h) : ℂ) •
        ∑ k : Ch01.Band (2*h),
          star (Ch06Ext.twistedCharacter (2*h) (b ν) k x) •
            (A05.creation h ν k) (A02.ket S) := by
  rw [A05.liftedAnnihilation]
  simp only [map_smulₛₗ, map_sum, LinearMap.smul_apply, map_smul]
  simp_rw [A05.creation_adjoint]
  rfl
end Bosonize.Ch20
