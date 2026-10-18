import BosonizeStubs.V1S3FormalDuality

open Bosonize.V1S3 Bosonize.V1S2

private noncomputable def squeezed : Bosonize.Ch18.HyperbolicPair :=
  ⟨(5 : ℝ) / 4, (3 : ℝ) / 4, by norm_num⟩

private def zeroSqueeze : Bosonize.Ch18.HyperbolicPair :=
  ⟨1, 0, by norm_num⟩

example : gainD squeezed = 1 / 4 ∧ gainS squeezed = 4 := by
  norm_num [gainD, gainS, squeezed]

example : reflectHyperbolic zeroSqueeze = zeroSqueeze := by
  norm_num [reflectHyperbolic, zeroSqueeze]

example : reflectCharge (2, 1) = (2, -1) ∧ reflectCharge (2, 1) ≠ (2, 1) := by
  norm_num [reflectCharge]

example : rightOscillatorDegree (M := 0) (0 : Bosonize.A08.OscMode 0 →₀ ℕ) = 0 := by
  simp [rightOscillatorDegree]

example : rightOscillatorParity (M := 0)
    (0 : Bosonize.A08.OscMode 0 →₀ ℕ) = 1 := by
  simp [rightOscillatorParity, rightOscillatorDegree]


example : chargePhase 4 1 (1 : Position 4) = Complex.I := by
  have hroot : Bosonize.A01.canonicalRoot 4 = Complex.I := by
    unfold Bosonize.A01.canonicalRoot
    calc
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (4:ℂ)) =
          Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) := by congr 1; ring
      _ = Complex.I := Complex.exp_pi_div_two_mul_I
  have hx : (1 : Position 4).val = 1 := by
    exact @ZMod.val_one 4 ⟨by omega⟩
  simp [chargePhase, Bosonize.A01.integerCharacter, hroot, hx]

#print axioms reflectChargeEquiv
#print axioms chargeReflectionLinear
#print axioms oscillatorParityAlgHom
#print axioms oscillatorDualityAlgHom
#print axioms jointReflectionLinear
#print axioms dualOscSyntax
#print axioms dualCoeff
#print axioms dualSeries

private theorem phaseMinusOne : chargePhase 4 (-1) (1 : Position 4) = -Complex.I := by
  have h := chargePhase 4 1 (1 : Position 4)
  have hroot : Bosonize.A01.canonicalRoot 4 = Complex.I := by
    unfold Bosonize.A01.canonicalRoot
    calc
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (4:ℂ)) =
          Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) := by congr 1; ring
      _ = Complex.I := Complex.exp_pi_div_two_mul_I
  have hx : (1 : Position 4).val = 1 := by exact @ZMod.val_one 4 ⟨by omega⟩
  rw [chargePhase, Bosonize.A01.integerCharacter, hroot, hx]
  norm_num

example :
    chargeWordAction (reflectChargeWord (canonicalKleinD 2 4 (1 : Position 4)))
      (Finsupp.single ((0 : ℤ), (0 : ℤ)) (1 : ℂ)) =
    Complex.I • Finsupp.single ((1 : ℤ), (1 : ℤ)) (1 : ℂ) := by
  rw [chargeWordAction_basis_contract]
  have hroot : Bosonize.A01.canonicalRoot 4 = Complex.I := by
    unfold Bosonize.A01.canonicalRoot
    calc
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (4:ℂ)) =
          Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) := by congr 1; ring
      _ = Complex.I := Complex.exp_pi_div_two_mul_I
  have hx : (1 : Position 4).val = 1 := by exact @ZMod.val_one 4 ⟨by omega⟩
  norm_num [reflectChargeWord, reflectCharge, canonicalKleinD, kleinD,
    chargeShiftD, chargeShiftDEquiv, chargeGauge, chargeGaugeExponent,
    aD, chargePhase, Bosonize.A01.integerCharacter, hroot, hx]

example :
    chargeWordAction (reflectChargeWord (kleinD 4 (1 : Position 4)))
      (Finsupp.single ((0 : ℤ), (0 : ℤ)) (1 : ℂ)) =
    (-Complex.I) • Finsupp.single ((1 : ℤ), (1 : ℤ)) (1 : ℂ) := by
  rw [chargeWordAction_basis_contract]
  have hroot : Bosonize.A01.canonicalRoot 4 = Complex.I := by
    unfold Bosonize.A01.canonicalRoot
    calc
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (4:ℂ)) =
          Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) := by congr 1; ring
      _ = Complex.I := Complex.exp_pi_div_two_mul_I
  have hx : (1 : Position 4).val = 1 := by exact @ZMod.val_one 4 ⟨by omega⟩
  norm_num [reflectChargeWord, reflectCharge, kleinD, chargeShiftDEquiv,
    chargeShiftD, chargeGauge, chargeGaugeExponent, aD, chargePhase,
    Bosonize.A01.integerCharacter, hroot, hx]
