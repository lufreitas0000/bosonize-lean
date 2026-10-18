import Bosonize.Core.V1S2FormalVertices

/-!
# V1-S3: formal duality and state-family transport

This additive interface is based on the promoted V1-S2 carrier.  Charge
operators are `ChargeWord`s, oscillator coefficients are finite-word
`OscSyntax` expressions evaluated in A08's free algebra, and formal vertices
are S2's multiset-valued coefficient series.  No quotient CCR algebra or
finite-CAR implementation is introduced here.
-/

namespace Bosonize.V1S3

open Bosonize.V1S2

abbrev Charge := Bosonize.V1S2.Charge

def reflectCharge (N : Charge) : Charge := (N.1, -N.2)

noncomputable def oscillatorParityAlgHom {M : ℕ} :
    Bosonize.A08.OscPoly M →ₐ[ℂ] Bosonize.A08.OscPoly M :=
  MvPolynomial.aeval (fun p =>
    if p.1 == Bosonize.A06.Orientation.right then -MvPolynomial.X p
    else MvPolynomial.X p)

theorem reflectCharge_involutive (N : Charge) :
    reflectCharge (reflectCharge N) = N := by
  rcases N with ⟨r, l⟩
  simp [reflectCharge]

def reflectChargeEquiv : Charge ≃ Charge where
  toFun := reflectCharge
  invFun := reflectCharge
  left_inv := reflectCharge_involutive
  right_inv := reflectCharge_involutive


noncomputable def chargeReflectionLinear : ChargeVec →ₗ[ℂ] ChargeVec :=
  (Finsupp.domCongr reflectChargeEquiv).toLinearEquiv (by
    intro z v
    ext N
    simp [Finsupp.domCongr_apply]) |>.toLinearMap

noncomputable def jointReflectionLinear {M : ℕ} :
    JointCarrier M →ₗ[ℂ] JointCarrier M :=
  TensorProduct.map chargeReflectionLinear oscillatorParityAlgHom.toLinearMap

def rightOscillatorDegree {M : ℕ}
    (k : Bosonize.A08.OscMode M →₀ ℕ) : ℕ :=
  ∑ p ∈ k.support,
    if p.1 = Bosonize.A06.Orientation.right then k p else 0

def rightOscillatorParity {M : ℕ}
    (k : Bosonize.A08.OscMode M →₀ ℕ) : ℂ :=
  (-1 : ℂ) ^ rightOscillatorDegree k




theorem chargeReflectionLinear_basis (N : Charge) :
    chargeReflectionLinear (Finsupp.single N (1 : ℂ)) =
      Finsupp.single (reflectCharge N) 1 := by
  classical
  simp [chargeReflectionLinear, reflectChargeEquiv, Finsupp.domCongr_apply, reflectCharge]

theorem jointReflection_basis {M : ℕ} (N : Charge)
    (k : Bosonize.A08.OscMode M →₀ ℕ) :
    jointReflectionLinear (jointBasisOf M (N, k)) =
      rightOscillatorParity k • jointBasisOf M (reflectCharge N, k) := by
  sorry

theorem polynomial_vacuum_parity_invariant {M : ℕ} :
    oscillatorParityAlgHom (1 : Bosonize.A08.OscPoly M) = 1 :=
  by simp [oscillatorParityAlgHom]

def reflectHyperbolic (P : Bosonize.Ch18.HyperbolicPair) :
    Bosonize.Ch18.HyperbolicPair where
  c := P.c
  s := -P.s
  hyperbolic_id := by rw [neg_sq]; exact P.hyperbolic_id

theorem reflectHyperbolic_involutive (P : Bosonize.Ch18.HyperbolicPair) :
    reflectHyperbolic (reflectHyperbolic P) = P := by
  cases P
  simp [reflectHyperbolic]

theorem gain_exchange (P : Bosonize.Ch18.HyperbolicPair) :
    gainD (reflectHyperbolic P) = gainS P ∧
    gainS (reflectHyperbolic P) = gainD P := by
  constructor
  · simp [gainD, gainS, reflectHyperbolic]
  · simp [gainD, gainS, reflectHyperbolic]
    ring

theorem gains_reciprocal (P : Bosonize.Ch18.HyperbolicPair) :
    gainD P * gainS P = 1 := by
  have h := P.hyperbolic_id
  simp [gainD, gainS]
  nlinarith

def reflectChargeWord (w : ChargeWord) : ChargeWord where
  target :=
    { toFun := fun N => reflectCharge (w.target (reflectCharge N))
      invFun := fun N => reflectCharge (w.target.symm (reflectCharge N))
      left_inv := by
        intro N
        simp [reflectCharge_involutive]
      right_inv := by
        intro N
        simp [reflectCharge_involutive] }
  amplitude := fun N => w.amplitude (reflectCharge N)

def dualOscGen {M : ℕ} (g : Bosonize.A08.OscGen M) :
    Bosonize.A08.OscGen M :=
  (g.1, (if g.2.1 == Bosonize.A06.Orientation.right then
    Bosonize.A06.Orientation.right else Bosonize.A06.Orientation.left, g.2.2))

def dualOscSign {M : ℕ} (g : Bosonize.A08.OscGen M) : ℂ :=
  if g.2.1 == Bosonize.A06.Orientation.right then -1 else 1

noncomputable def oscillatorDualityAlgHom {M : ℕ} :
    Bosonize.A08.OscAlgebra M →ₐ[ℂ] Bosonize.A08.OscAlgebra M :=
  FreeAlgebra.lift ℂ (fun g =>
    (dualOscSign g) • FreeAlgebra.ι ℂ (dualOscGen g))


def dualOscWord {M : ℕ} : Bosonize.A08.OscWord M → Bosonize.A08.OscWord M
  | [] => []
  | g :: gs => dualOscGen g :: dualOscWord gs

def dualOscWordSign {M : ℕ} : Bosonize.A08.OscWord M → ℂ
  | [] => 1
  | g :: gs => dualOscSign g * dualOscWordSign gs

noncomputable def dualOscLinearForm {M : ℕ}
    (f : Bosonize.V1S1.OscLinearForm M) : Bosonize.V1S1.OscLinearForm M := by
  classical
  exact f.sum fun g z =>
    (dualOscSign g * z) • Finsupp.single (dualOscGen g) (1 : ℂ)

noncomputable def dualOscSyntax {M : ℕ} (a : OscSyntax M) : OscSyntax M := by
  classical
  exact MonoidAlgebra.ofCoeff
    (Finsupp.sum a.coeff fun w z =>
      Finsupp.single (dualOscWord w) (dualOscWordSign w * z))

noncomputable def dualCoeff {M : ℕ} (a : vertexCoeff M) : vertexCoeff M :=
  (reflectChargeWord a.1, dualOscSyntax a.2)

noncomputable def vertexCoeffOne {M : ℕ} : vertexCoeff M :=
  (⟨Equiv.refl Charge, fun _ => 1⟩, 1)

def vertexCoeffScale {M : ℕ} (z : ℂ) (a : vertexCoeff M) : vertexCoeff M :=
  (ChargeWord.scale z a.1, a.2)

noncomputable def D_P {M : ℕ} (_P : Bosonize.Ch18.HyperbolicPair) :
    vertexCoeff M → vertexCoeff M := dualCoeff

noncomputable def dualSeries {M : ℕ} (A : VertexSeries M) : VertexSeries M :=
  fun n => (A n).map dualCoeff

noncomputable def vertexMultisetAction {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (m : Multiset (vertexCoeff M)) :
    Module.End ℂ (JointCarrier M) :=
  (m.map (jointCoeffAction P)).sum

noncomputable def representedSeries {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (A : VertexSeries M) :
    FormalSeries (Module.End ℂ (JointCarrier M)) :=
  fun n => vertexMultisetAction P (A n)

noncomputable def representedSeriesMul {M : ℕ}
    (A B : FormalSeries (Module.End ℂ (JointCarrier M))) :
    FormalSeries (Module.End ℂ (JointCarrier M)) := fun n =>
  ∑ k ∈ Finset.range (n + 1), (A k).comp (B (n - k))

theorem dualOsc_generator_action_contract {M : ℕ} (g : Bosonize.A08.OscGen M) :
    dualOscSign g • (MonoidAlgebra.single [dualOscGen g] (1 : ℂ) : OscSyntax M) =
      (if g.2.1 == Bosonize.A06.Orientation.right then
        -MonoidAlgebra.single [dualOscGen g] (1 : ℂ)
      else MonoidAlgebra.single [dualOscGen g] (1 : ℂ)) := by
  by_cases hg : g.2.1 == Bosonize.A06.Orientation.right <;>
    simp [dualOscSign, hg]

theorem dualOscSyntax_preserves_one_contract {M : ℕ} :
    dualOscSyntax (1 : OscSyntax M) = 1 := by
  sorry

theorem dualOscSyntax_preserves_mul_contract {M : ℕ} (a b : OscSyntax M) :
    dualOscSyntax (a * b) = dualOscSyntax a * dualOscSyntax b := by
  sorry

theorem dualOscSyntax_preserves_dagger_contract {M : ℕ} (a : OscSyntax M) :
    dualOscSyntax (oscSyntaxDagger a) = oscSyntaxDagger (dualOscSyntax a) := by
  sorry

theorem dualOscSyntax_involutive_contract {M : ℕ} (a : OscSyntax M) :
    dualOscSyntax (dualOscSyntax a) = a := by
  sorry

theorem oscillatorParityAlgHom_one {M : ℕ} :
    oscillatorParityAlgHom (1 : Bosonize.A08.OscPoly M) = 1 := by
  simp [oscillatorParityAlgHom]

theorem oscillatorParityAlgHom_involutive {M : ℕ}
    (p : Bosonize.A08.OscPoly M) :
    oscillatorParityAlgHom (oscillatorParityAlgHom p) = p := by
  sorry

theorem oscillatorParityAlgHom_creation {M : ℕ} (ν : Bosonize.A06.Orientation)
    (m : Fin M) :
    oscillatorParityAlgHom (MvPolynomial.X (ν, m)) =
      (if ν = Bosonize.A06.Orientation.right then -1 else 1) •
        MvPolynomial.X (ν, m) := by
  sorry

theorem oscillatorDuality_generator {M : ℕ} (g : Bosonize.A08.OscGen M) :
    oscillatorDualityAlgHom (FreeAlgebra.ι ℂ g) =
      dualOscSign g • FreeAlgebra.ι ℂ (dualOscGen g) := by
  simp [oscillatorDualityAlgHom]

theorem oscillatorDuality_syntax_compatibility_contract {M : ℕ}
    (a : Bosonize.A08.OscAlgebra M) :
    oscFreeToSyntax M (oscillatorDualityAlgHom a) =
      dualOscSyntax (oscFreeToSyntax M a) := by
  sorry

theorem oscillator_bogoliubov_intertwining_contract {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (a : Bosonize.A08.OscAlgebra M) :
    oscillatorDualityAlgHom
      (Bosonize.A08.bogoliubovMap M P.c (-P.s) a) =
    Bosonize.A08.bogoliubovMap M (reflectHyperbolic P).c
      (-(reflectHyperbolic P).s)
      (oscillatorDualityAlgHom a) := by
  sorry

theorem dressed_right_generator_duality {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (m : Fin M) :
    oscillatorDualityAlgHom
      (Bosonize.V1S1.dressedLinearElement P.c P.s
        (Finsupp.single (true, (Bosonize.A06.Orientation.right, m)) 1)) =
      -Bosonize.V1S1.dressedLinearElement P.c (-P.s)
        (Finsupp.single (true, (Bosonize.A06.Orientation.right, m)) 1) := by
  sorry

theorem dressed_left_generator_duality {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (m : Fin M) :
    oscillatorDualityAlgHom
      (Bosonize.V1S1.dressedLinearElement P.c P.s
        (Finsupp.single (true, (Bosonize.A06.Orientation.left, m)) 1)) =
      Bosonize.V1S1.dressedLinearElement P.c (-P.s)
        (Finsupp.single (true, (Bosonize.A06.Orientation.left, m)) 1) := by
  sorry

theorem jointReflectionLinear_involutive {M : ℕ} (v : JointCarrier M) :
    jointReflectionLinear (jointReflectionLinear v) = v := by
  sorry

theorem reflectChargeWord_preserves_comp_contract (a b : ChargeWord) :
    reflectChargeWord (ChargeWord.comp a b) =
      ChargeWord.comp (reflectChargeWord a) (reflectChargeWord b) := by
  sorry

theorem reflectChargeWord_basis_action (w : ChargeWord) (N : Charge) :
    chargeWordAction (reflectChargeWord w)
        (Finsupp.single N (1 : ℂ)) =
      chargeReflectionLinear
        (chargeWordAction w (Finsupp.single (reflectCharge N) 1)) := by
  sorry

theorem reflectChargeWord_diagonal_observable (f : Charge → ℂ) :
    reflectChargeWord ⟨Equiv.refl Charge, f⟩ =
      ⟨Equiv.refl Charge, fun N => f (reflectCharge N)⟩ := by
  sorry

theorem reflectChargeWord_preserves_adjoint_contract (a : ChargeWord) :
    reflectChargeWord (ChargeWord.adjoint a) =
      ChargeWord.adjoint (reflectChargeWord a) := by
  sorry

theorem dualCoeff_preserves_mul_contract {M : ℕ} (a b : vertexCoeff M) :
    dualCoeff (vertexCoeffMul a b) = vertexCoeffMul (dualCoeff a) (dualCoeff b) := by
  sorry

theorem dualCoeff_preserves_adjoint_contract {M : ℕ} (a : vertexCoeff M) :
    dualCoeff (vertexCoeffAdjoint a) = vertexCoeffAdjoint (dualCoeff a) := by
  sorry

theorem dualCoeff_involutive_contract {M : ℕ} (a : vertexCoeff M) :
    dualCoeff (dualCoeff a) = a := by
  sorry

theorem D_P_scalar_contract {M : ℕ} (P : Bosonize.Ch18.HyperbolicPair)
    (z : ℂ) (a : vertexCoeff M) :
    D_P P (vertexCoeffScale z a) = vertexCoeffScale z (D_P P a) := by
  sorry

theorem D_P_unit_contract {M : ℕ} (P : Bosonize.Ch18.HyperbolicPair) :
    D_P (M := M) P vertexCoeffOne = vertexCoeffOne := by
  sorry

theorem D_twice_typed_contract {M : ℕ} (P : Bosonize.Ch18.HyperbolicPair)
    (a : vertexCoeff M) :
    D_P (reflectHyperbolic P) (D_P P a) = a := by
  exact dualCoeff_involutive_contract a

theorem represented_action_intertwining_contract {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (a : vertexCoeff M) :
    jointCoeffAction (reflectHyperbolic P) (dualCoeff a) =
      (jointReflectionLinear.comp (jointCoeffAction P a)).comp
        jointReflectionLinear := by
  sorry

theorem represented_action_kernel_transport_contract {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (a : vertexCoeff M) :
    jointCoeffAction P a = 0 ↔
      jointCoeffAction (reflectHyperbolic P) (dualCoeff a) = 0 := by
  sorry

theorem representedSeries_intertwining_contract {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (A : VertexSeries M) (n : ℕ) :
    representedSeries (reflectHyperbolic P) (dualSeries A) n =
      (jointReflectionLinear.comp (representedSeries P A n)).comp
        jointReflectionLinear := by
  sorry

theorem representedSeries_mul_contract {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (A B : VertexSeries M) :
    representedSeries P (vertexSeriesMul A B) =
      representedSeriesMul (representedSeries P A) (representedSeries P B) := by
  sorry

theorem joint_functional_transport_from_action {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (N : Charge) (a : vertexCoeff M) :
    jointCoeffFunctional (reflectHyperbolic P) (reflectCharge N) (dualCoeff a) =
      jointCoeffFunctional P N a := by
  sorry

theorem dualSeries_product_contract {M : ℕ} (A B : VertexSeries M) :
    dualSeries (vertexSeriesMul A B) =
      vertexSeriesMul (dualSeries A) (dualSeries B) := by
  sorry

theorem dualSeries_adjoint_contract {M : ℕ} (A : VertexSeries M) :
    dualSeries (vertexSeriesAdjoint A) =
      vertexSeriesAdjoint (dualSeries A) := by
  sorry

theorem dualSeries_involutive_contract {M : ℕ} (A : VertexSeries M) :
    dualSeries (dualSeries A) = A := by
  sorry

theorem canonicalKleinD_reflection_contract {L h : ℕ} (x : Position L) :
    reflectChargeWord (canonicalKleinD h L x) =
      ChargeWord.scale ((Bosonize.A01.canonicalRoot L) ^ (x.val : ℤ))
        (canonicalKleinSAdj h L x) := by
  sorry

theorem canonicalKleinS_reflection_contract {L h : ℕ} (x : Position L) :
    reflectChargeWord (canonicalKleinS h L x) =
      ChargeWord.scale ((Bosonize.A01.canonicalRoot L) ^ (x.val : ℤ))
        (canonicalKleinDAdj h L x) := by
  sorry

theorem simplifiedKleinD_reflection_sign_contract {L : ℕ} (x : Position L) :
    reflectChargeWord (kleinD L x) =
      ChargeWord.scale (-((Bosonize.A01.canonicalRoot L) ^ (x.val : ℤ)))
        (kleinSAdj L x) := by
  sorry

theorem simplifiedKleinS_reflection_sign_contract {L : ℕ} (x : Position L) :
    reflectChargeWord (kleinS L x) =
      ChargeWord.scale (-((Bosonize.A01.canonicalRoot L) ^ (x.val : ℤ)))
        (kleinDAdj L x) := by
  sorry

theorem canonical_degree_zero_D_action {h : ℕ} (N : Charge)
    (x : Position (2 * h)) :
    chargeWordAction (reflectChargeWord (canonicalKleinD h (2 * h) x))
        (Finsupp.single N (1 : ℂ)) =
      ((Bosonize.A01.canonicalRoot (2*h)) ^ (x.val : ℤ)) •
        chargeWordAction (canonicalKleinSAdj h (2 * h) x)
          (Finsupp.single N (1 : ℂ)) := by
  sorry

theorem duality_charge_vector_contract (N : Charge) :
    reflectCharge (reflectCharge N) = N := reflectCharge_involutive N

theorem oscillator_field_D_duality {M L : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (x : Position L) :
    dualOscLinearForm (xDForm (M := M) (L := L) P x) =
      -xSForm (M := M) (L := L) (reflectHyperbolic P) x := by
  sorry

theorem oscillator_field_S_duality {M L : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (x : Position L) :
    dualOscLinearForm (xSForm (M := M) (L := L) P x) =
      -xDForm (M := M) (L := L) (reflectHyperbolic P) x := by
  sorry

theorem chargeWord_reflection_source_first (w : ChargeWord) (N : Charge) :
    chargeWordAction (reflectChargeWord w) (Finsupp.single N (1 : ℂ)) =
      w.amplitude (reflectCharge N) •
        Finsupp.single (reflectCharge (w.target (reflectCharge N))) 1 := by
  sorry

theorem chargeBasisExpectation_reflection (N : Charge) (w : ChargeWord) :
    chargeBasisExpectation (reflectCharge N) (reflectChargeWord w) =
      chargeBasisExpectation N w := by
  sorry

theorem duality_vertex_D_contract {M h : ℕ} (hh : 0 < h)
    (P : Bosonize.Ch18.HyperbolicPair) (x : Position (2 * h)) :
    dualSeries (vertexWeyl (M := M) hh P x false) =
      vertexSeriesScalarMul
        (fun n => if n = 0 then
          ((Bosonize.A01.canonicalRoot (2*h)) ^ (x.val : ℤ)) else 0)
        (vertexWeylAdj (M := M) hh (reflectHyperbolic P) x true) := by
  sorry

theorem duality_vertex_S_contract {M h : ℕ} (hh : 0 < h)
    (P : Bosonize.Ch18.HyperbolicPair) (x : Position (2 * h)) :
    dualSeries (vertexWeyl (M := M) hh P x true) =
      vertexSeriesScalarMul
        (fun n => if n = 0 then
          ((Bosonize.A01.canonicalRoot (2*h)) ^ (x.val : ℤ)) else 0)
        (vertexWeylAdj (M := M) hh (reflectHyperbolic P) x false) := by
  sorry

theorem duality_vertex_D_t0_contract {M h : ℕ} (hh : 0 < h)
    (P : Bosonize.Ch18.HyperbolicPair) (x : Position (2 * h)) :
    (dualSeries (vertexWeyl (M := M) hh P x false)) 0 =
      (vertexSeriesScalarMul
        (fun n => if n = 0 then
          ((Bosonize.A01.canonicalRoot (2*h)) ^ (x.val : ℤ)) else 0)
        (vertexWeylAdj (M := M) hh (reflectHyperbolic P) x true)) 0 := by
  sorry

theorem dressed_normal_multiplier_exchange {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) :
    dressedNormalMultiplier (M := M) (reflectHyperbolic P) false =
      dressedNormalMultiplier (M := M) P true ∧
    dressedNormalMultiplier (M := M) (reflectHyperbolic P) true =
      dressedNormalMultiplier (M := M) P false := by
  sorry

theorem bare_normal_multiplier_self_adjoint {M : ℕ} (n : ℕ) :
    star (bareNormalMultiplier M n) = bareNormalMultiplier M n := by
  sorry

theorem dressed_normal_vertex_D_contract {M h : ℕ} (hh : 0 < h)
    (P : Bosonize.Ch18.HyperbolicPair) (x : Position (2 * h)) :
    dualSeries (vertexWeylDressedNormal (M := M) hh P x false) =
      vertexSeriesScalarMul
        (fun n => if n = 0 then
          ((Bosonize.A01.canonicalRoot (2*h)) ^ (x.val : ℤ)) else 0)
        (vertexSeriesAdjoint
          (vertexWeylDressedNormal (M := M) hh (reflectHyperbolic P) x true)) := by
  sorry

theorem bare_normal_vertex_D_contract {M h : ℕ} (hh : 0 < h)
    (P : Bosonize.Ch18.HyperbolicPair) (x : Position (2 * h)) :
    dualSeries (vertexWeylBareNormal (M := M) hh P x false) =
      vertexSeriesScalarMul
        (fun n => if n = 0 then
          ((Bosonize.A01.canonicalRoot (2*h)) ^ (x.val : ℤ)) else 0)
        (vertexSeriesAdjoint
          (vertexWeylBareNormal (M := M) hh (reflectHyperbolic P) x true)) := by
  sorry

theorem duality_state_family_contract {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (N : Charge) (a : vertexCoeff M) :
    jointCoeffFunctional (reflectHyperbolic P) (reflectCharge N) (dualCoeff a) =
      jointCoeffFunctional P N a := by
  sorry

theorem duality_state_family_series_contract {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (N : Charge) (A : VertexSeries M) :
    jointSeriesFunctional (reflectHyperbolic P) (reflectCharge N) (dualSeries A) =
      jointSeriesFunctional P N A := by
  sorry

theorem duality_ordered_product_transport {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (N : Charge)
    (A B : VertexSeries M) :
    jointSeriesFunctional (reflectHyperbolic P) (reflectCharge N)
        (vertexSeriesMul (dualSeries A) (dualSeries B)) =
      jointSeriesFunctional P N (vertexSeriesMul A B) := by
  sorry

theorem duality_ordered_vertex_adjoint_transport {M h : ℕ}
    (hh : 0 < h) (P : Bosonize.Ch18.HyperbolicPair) (N : Charge)
    (x y : Position (2 * h)) (channel : Bool) :
    jointSeriesFunctional (reflectHyperbolic P) (reflectCharge N)
        (vertexSeriesMul
          (vertexWeyl (M := M) hh (reflectHyperbolic P) x (!channel))
          (vertexWeylAdj (M := M) hh (reflectHyperbolic P) y (!channel))) =
      scalarSeriesMul
        (fun n => if n = 0 then
          ((Bosonize.A01.canonicalRoot (2*h)) ^ (x.val : ℤ) *
            star ((Bosonize.A01.canonicalRoot (2*h)) ^ (y.val : ℤ))) else 0)
        (jointSeriesFunctional P N
          (vertexSeriesMul
            (vertexWeylAdj (M := M) hh P x channel)
            (vertexWeyl (M := M) hh P y channel))) := by
  sorry

theorem dressed_normal_vertex_adjoint_transport {M h : ℕ}
    (hh : 0 < h) (P : Bosonize.Ch18.HyperbolicPair) (N : Charge)
    (x y : Position (2 * h)) (channel : Bool) :
    jointSeriesFunctional (reflectHyperbolic P) (reflectCharge N)
        (vertexSeriesMul
          (vertexWeylDressedNormal (M := M) hh (reflectHyperbolic P) x (!channel))
          (vertexSeriesAdjoint
            (vertexWeylDressedNormal (M := M) hh (reflectHyperbolic P) y (!channel)))) =
      scalarSeriesMul
        (fun n => if n = 0 then
          ((Bosonize.A01.canonicalRoot (2*h)) ^ (x.val : ℤ) *
            star ((Bosonize.A01.canonicalRoot (2*h)) ^ (y.val : ℤ))) else 0)
        (jointSeriesFunctional P N
          (vertexSeriesMul
            (vertexSeriesAdjoint (vertexWeylDressedNormal (M := M) hh P x channel))
            (vertexWeylDressedNormal (M := M) hh P y channel))) := by
  sorry

theorem bare_normal_vertex_adjoint_transport {M h : ℕ}
    (hh : 0 < h) (P : Bosonize.Ch18.HyperbolicPair) (N : Charge)
    (x y : Position (2 * h)) (channel : Bool) :
    jointSeriesFunctional (reflectHyperbolic P) (reflectCharge N)
        (vertexSeriesMul
          (vertexWeylBareNormal (M := M) hh (reflectHyperbolic P) x (!channel))
          (vertexSeriesAdjoint
            (vertexWeylBareNormal (M := M) hh (reflectHyperbolic P) y (!channel)))) =
      scalarSeriesMul
        (fun n => if n = 0 then
          ((Bosonize.A01.canonicalRoot (2*h)) ^ (x.val : ℤ) *
            star ((Bosonize.A01.canonicalRoot (2*h)) ^ (y.val : ℤ))) else 0)
        (jointSeriesFunctional P N
          (vertexSeriesMul
            (vertexSeriesAdjoint (vertexWeylBareNormal (M := M) hh P x channel))
            (vertexWeylBareNormal (M := M) hh P y channel))) := by
  sorry

end Bosonize.V1S3
