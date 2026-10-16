import Bosonize.Core.Ch14Mandelstam
import Bosonize.Core.Ch16FieldHamiltonian
import BosonizeStubs.Ch20CDW

open scoped BigOperators Classical
open Bosonize
namespace Bosonize.Ch20ScalarScratch

noncomputable local instance modeLinearOrder : LinearOrder (A05.Mode (Fin 2) 2) := A05.localModeLinearOrder (σ:=Fin 2) 2
noncomputable local instance modeLT : LT (A05.Mode (Fin 2) 2) := A05.localModeLT (σ:=Fin 2) 2
noncomputable local instance modeLE : LE (A05.Mode (Fin 2) 2) := A05.localModeLE (σ:=Fin 2) 2
noncomputable local instance modeDecEq : DecidableEq (A05.Mode (Fin 2) 2) := A05.localModeDecidableEq (σ:=Fin 2) 2
noncomputable local instance fixedModeOrder : LinearOrder (Fin 2 × Ch01.Band 4) := A05.localModeLinearOrder (σ:=Fin 2) 2
noncomputable local instance fixedModeLT : LT (Fin 2 × Ch01.Band 4) := A05.localModeLT (σ:=Fin 2) 2
noncomputable local instance fixedModeLE : LE (Fin 2 × Ch01.Band 4) := A05.localModeLE (σ:=Fin 2) 2
noncomputable local instance fixedModeDecEq : DecidableEq (Fin 2 × Ch01.Band 4) := A05.localModeDecidableEq (σ:=Fin 2) 2

def mn : Ch01.Band 4 := ⟨-1, by norm_num [Ch01.inBandPredicate]⟩
def m1 : Ch01.Band 4 := ⟨1, by norm_num [Ch01.inBandPredicate]⟩

private noncomputable def residual_m1_f : ℂ :=
  Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) mn 1 *
    Ch04.fermionSign (1,mn) (A05.groundConfiguration 2 Bosonize.Ch20.witnessZero) *
    star (A01.normalization 4 : ℂ) *
    star (Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) m1 1) *
    Ch04.fermionSign (0,m1) ((A05.groundConfiguration 2 Bosonize.Ch20.witnessZero).erase (1,mn))

lemma residual_m1_f_nonzero : residual_m1_f ≠ 0 := by
  have hnorm : (A01.normalization 4 : ℂ) ≠ 0 := by
    norm_num [A01.normalization]
  have hsign₁ : Ch04.fermionSign (1,mn)
      (A05.groundConfiguration 2 Bosonize.Ch20.witnessZero) ≠ 0 :=
    Ch04.fermion_sign_ne_zero _ _
  have hsign₂ : Ch04.fermionSign (0,m1)
      ((A05.groundConfiguration 2 Bosonize.Ch20.witnessZero).erase (1,mn)) ≠ 0 :=
    Ch04.fermion_sign_ne_zero _ _
  have hchar₁ : Ch06Ext.twistedCharacter 4
      (Ch06Ext.periodicTwist 4) mn 1 ≠ 0 := by
    unfold Ch06Ext.twistedCharacter
    apply mul_ne_zero
    · unfold Ch06Ext.liftPhase Ch06Ext.periodicTwist
      simp
    · unfold A01.integerCharacter
      have hroot : A01.canonicalRoot 4 ≠ 0 := by
        unfold A01.canonicalRoot
        exact Complex.exp_ne_zero _
      exact zpow_ne_zero _ hroot
  have hchar₂ : Ch06Ext.twistedCharacter 4
      (Ch06Ext.periodicTwist 4) m1 1 ≠ 0 := by
    unfold Ch06Ext.twistedCharacter
    apply mul_ne_zero
    · unfold Ch06Ext.liftPhase Ch06Ext.periodicTwist
      simp
    · unfold A01.integerCharacter
      have hroot : A01.canonicalRoot 4 ≠ 0 := by
        unfold A01.canonicalRoot
        exact Complex.exp_ne_zero _
      exact zpow_ne_zero _ hroot
  have hnormStar : star (A01.normalization 4 : ℂ) ≠ 0 := by
    simpa using hnorm
  have hchar₂Star : star (Ch06Ext.twistedCharacter 4
      (Ch06Ext.periodicTwist 4) m1 1) ≠ 0 := by
    simpa using hchar₂
  unfold residual_m1_f
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hchar₁ hsign₁)
    hnormStar) hchar₂Star) hsign₂

end Bosonize.Ch20ScalarScratch
