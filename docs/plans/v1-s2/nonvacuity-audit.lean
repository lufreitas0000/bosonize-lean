import BosonizeStubs.V1S2FormalVertices
open Bosonize.V1S2
private def hp0 : Bosonize.Ch18.HyperbolicPair := ⟨1, 0, by norm_num⟩
private noncomputable def hpSqueezed : Bosonize.Ch18.HyperbolicPair := ⟨5/3, 4/3, by norm_num⟩
example : gainD hpSqueezed = 1/9 ∧ gainS hpSqueezed = 9 := by
  norm_num [gainD, gainS, hpSqueezed]
example (M : ℕ) :
    expectedWeylCorrelator (M := M) (h := 1) (by decide) hp0 (0, 0) 0 0 false 0 = 1/4 := by
  norm_num [expectedWeylCorrelator, Bosonize.A01.integerCharacter]
example (M : ℕ) :
    jointSeriesFunctional (M := M) hp0 (0, 0)
      (vertexSeriesMul (vertexWeylAdj (h := 1) (by decide) hp0 0 false)
        (vertexWeyl (h := 1) (by decide) hp0 0 false)) 0 ≠ 0 := by
  rw [coefficientwise_weyl_correlator_contract]
  norm_num [expectedWeylCorrelator, Bosonize.A01.integerCharacter]
