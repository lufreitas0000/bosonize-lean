import Mathlib.Analysis.Fourier.ZMod
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.NormNum

/-! Audit witnesses only; this is not the chapter 3 interface. -/

example : IsPrimitiveRoot (4 : ZMod 15) 2 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  exact orderOf_eq_prime (by decide) (by decide)

example : IsUnit (2 : ZMod 15) := by
  exact ⟨⟨2, 8, by decide, by decide⟩, rfl⟩

example : (∑ j ∈ Finset.range 2, (4 : ZMod 15) ^ j) ≠ 0 := by
  decide

#check ZMod.dft
#check ZMod.dft_apply
#check ZMod.invDFT_apply
#check ZMod.dft_dft
#check IsPrimitiveRoot.geom_sum_eq_zero
