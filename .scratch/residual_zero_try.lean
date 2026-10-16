import BosonizeStubs.Ch20CDW
open scoped BigOperators Classical
namespace Bosonize.Ch20ResidualScratch
variable {σ : Type*} [Fintype σ] [LinearOrder σ]
noncomputable local instance modeOrd (h : ℕ) : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
noncomputable local instance modeDecEq (h : ℕ) : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq
lemma fieldKet (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (ν : σ) (x : ℤ) (S : A05.Occupation σ h) :
    A05.liftedAnnihilation h b ν x (A02.ket S) =
      (A01.normalization (2*h) : ℂ) • ∑ k : Ch01.Band (2*h),
        if (ν,k) ∈ S then
          (Ch06Ext.twistedCharacter (2*h) (b ν) k x * Ch04.fermionSign (ν,k) S) •
            A02.ket (S.erase (ν,k))
        else 0 := by
  simp only [A05.liftedAnnihilation, LinearMap.smul_apply,
    LinearMap.sum_apply, A05.annihilation, Ch04.annihilation_ket]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hk
  · simp only [smul_smul]
  · simp [hk]
end Bosonize.Ch20ResidualScratch
