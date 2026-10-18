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
  classical
  simp only [jointBasisOf, Module.Basis.tensorProduct_apply]
  change chargeReflectionLinear (Finsupp.single N 1) ⊗ₜ[ℂ]
      oscillatorParityAlgHom ((MvPolynomial.monomial k) (1 : ℂ)) =
    rightOscillatorParity k •
      (Finsupp.single (reflectCharge N) 1 ⊗ₜ[ℂ] (MvPolynomial.monomial k) (1 : ℂ))
  rw [chargeReflectionLinear_basis, oscillatorParityAlgHom, MvPolynomial.aeval_monomial]
  have hprod :
      (k.prod fun i e =>
        (if i.1 = Bosonize.A06.Orientation.right then -MvPolynomial.X i else MvPolynomial.X i) ^ e) =
      MvPolynomial.C (rightOscillatorParity k) *
        (k.prod fun i e => MvPolynomial.X i ^ e) := by
    classical
    unfold Finsupp.prod rightOscillatorParity rightOscillatorDegree
    have hfactor (i : Bosonize.A08.OscMode M) (e : ℕ) :
        (if i.1 = Bosonize.A06.Orientation.right then -MvPolynomial.X i else MvPolynomial.X i) ^ e =
        MvPolynomial.C ((-1 : ℂ) ^ (if i.1 = Bosonize.A06.Orientation.right then e else 0)) *
          MvPolynomial.X i ^ e := by
      by_cases hir : i.1 = Bosonize.A06.Orientation.right
      · simp only [if_pos hir]
        rw [show -MvPolynomial.X i = MvPolynomial.C (-1 : ℂ) * MvPolynomial.X i by simp,
          mul_pow, ← map_pow (MvPolynomial.C : ℂ →+* MvPolynomial (Bosonize.A08.OscMode M) ℂ)]
      · rw [if_neg hir]
        simp [hir]
    calc
      (∏ i ∈ k.support,
          (if i.1 = Bosonize.A06.Orientation.right then
            -MvPolynomial.X i else MvPolynomial.X i) ^ k i) =
          ∏ i ∈ k.support,
            (MvPolynomial.C ((-1 : ℂ) ^ (if i.1 = Bosonize.A06.Orientation.right then k i else 0)) *
              MvPolynomial.X i ^ k i) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hfactor i (k i)
      _ = (∏ i ∈ k.support,
            MvPolynomial.C ((-1 : ℂ) ^ (if i.1 = Bosonize.A06.Orientation.right then k i else 0))) *
          (∏ i ∈ k.support, MvPolynomial.X i ^ k i) := Finset.prod_mul_distrib
      _ = MvPolynomial.C
            (∏ i ∈ k.support, (-1 : ℂ) ^ (if i.1 = Bosonize.A06.Orientation.right then k i else 0)) *
          (∏ i ∈ k.support, MvPolynomial.X i ^ k i) := by
        rw [← map_prod (MvPolynomial.C : ℂ →+* MvPolynomial (Bosonize.A08.OscMode M) ℂ)]
      _ = MvPolynomial.C
            ((-1 : ℂ) ^ ∑ i ∈ k.support,
              if i.1 = Bosonize.A06.Orientation.right then k i else 0) *
          (∏ i ∈ k.support, MvPolynomial.X i ^ k i) := by
        rw [Finset.prod_pow_eq_pow_sum]

  rw [← TensorProduct.tmul_smul]
  simp only [map_one, one_mul, beq_iff_eq]
  rw [hprod, MvPolynomial.monomial_eq]
  simpa [rightOscillatorParity, Finsupp.prod, MvPolynomial.smul_eq_C_mul]

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
  classical
  rw [MonoidAlgebra.one_def]
  simp [dualOscSyntax, dualOscWord, dualOscWordSign, Finsupp.sum_single_index]
  change MonoidAlgebra.single ([] : List (Bosonize.A08.OscGen M)) (1 : ℂ) =
    MonoidAlgebra.single ([] : List (Bosonize.A08.OscGen M)) (1 : ℂ)
  rfl

theorem dualOscSyntax_preserves_mul_contract {M : ℕ} (a b : OscSyntax M) :
    dualOscSyntax (a * b) = dualOscSyntax a * dualOscSyntax b := by
  classical
  have hzero : dualOscSyntax (0 : OscSyntax M) = 0 := by simp [dualOscSyntax]
  have hadd (x y : OscSyntax M) :
      dualOscSyntax (x + y) = dualOscSyntax x + dualOscSyntax y := by
    simp only [dualOscSyntax, MonoidAlgebra.coeff_add]
    rw [Finsupp.sum_add_index' (by intro w; simp)
      (by intro w z t; simp [mul_add, Finsupp.single_add])]
    exact MonoidAlgebra.ofCoeff_add _ _
  have hsingle (w : Bosonize.A08.OscWord M) (z : ℂ) :
      dualOscSyntax (MonoidAlgebra.single w z) =
        MonoidAlgebra.single (dualOscWord w) (dualOscWordSign w * z) := by
    simp [dualOscSyntax]
  have hword (w v : Bosonize.A08.OscWord M) :
      dualOscWord (w ++ v) = dualOscWord w ++ dualOscWord v := by
    induction w with
    | nil => rfl
    | cons g gs ih => simp [dualOscWord, ih]
  have hsign (w v : Bosonize.A08.OscWord M) :
      dualOscWordSign (w ++ v) = dualOscWordSign w * dualOscWordSign v := by
    induction w with
    | nil => simp [dualOscWordSign]
    | cons g gs ih => simp [dualOscWordSign, ih, mul_assoc]
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp [hzero]
  | add x y hx hy => rw [add_mul, hadd, hx, hy, hadd, add_mul]
  | single w z =>
      induction b using MonoidAlgebra.induction_linear with
      | zero => simp [hzero]
      | add x y hx hy => rw [mul_add, hadd, hx, hy, hadd, mul_add]
      | single v t =>
          simp only [MonoidAlgebra.single_mul_single, hsingle]
          change MonoidAlgebra.single (dualOscWord (w ++ v))
              (dualOscWordSign (w ++ v) * (z * t)) =
            MonoidAlgebra.single (dualOscWord w ++ dualOscWord v)
              (dualOscWordSign w * z * (dualOscWordSign v * t))
          rw [hsign, hword]
          congr 1
          ring

theorem dualOscSyntax_preserves_dagger_contract {M : ℕ} (a : OscSyntax M) :
    dualOscSyntax (oscSyntaxDagger a) = oscSyntaxDagger (dualOscSyntax a) := by
  classical
  have hzero (x : OscSyntax M) : oscSyntaxDagger (0 : OscSyntax M) = 0 := by
    simp [oscSyntaxDagger]
  have hadd (x y : OscSyntax M) :
      oscSyntaxDagger (x + y) = oscSyntaxDagger x + oscSyntaxDagger y := by
    simp only [oscSyntaxDagger, MonoidAlgebra.coeff_add]
    rw [Finsupp.sum_add_index' (by intro w; simp)
      (by intro w z t; simp [star_add, Finsupp.single_add])]
    exact MonoidAlgebra.ofCoeff_add _ _
  have hsingle (w : Bosonize.A08.OscWord M) (z : ℂ) :
      oscSyntaxDagger (MonoidAlgebra.single w z) =
        MonoidAlgebra.single (Bosonize.A08.wordDagger w) (star z) := by
    simp [oscSyntaxDagger]
  have happend (w v : Bosonize.A08.OscWord M) :
      dualOscWord (w ++ v) = dualOscWord w ++ dualOscWord v := by
    induction w with
    | nil => rfl
    | cons g gs ih => simp [dualOscWord, ih]
  have hsignAppend (w v : Bosonize.A08.OscWord M) :
      dualOscWordSign (w ++ v) = dualOscWordSign w * dualOscWordSign v := by
    induction w with
    | nil => simp [dualOscWordSign]
    | cons g gs ih => simp [dualOscWordSign, ih, mul_assoc]
  have hgen (g : Bosonize.A08.OscGen M) :
      dualOscGen (!g.1, g.2) = (! (dualOscGen g).1, (dualOscGen g).2) := by
    rcases g with ⟨b, ⟨ν, m⟩⟩
    cases b <;> cases ν <;> rfl
  have hgensign (g : Bosonize.A08.OscGen M) :
      dualOscSign (!g.1, g.2) = star (dualOscSign g) := by
    rcases g with ⟨b, ⟨ν, m⟩⟩
    cases b <;> cases ν <;> simp [dualOscSign]
  have hword (w : Bosonize.A08.OscWord M) :
      dualOscWord (Bosonize.A08.wordDagger w) =
        Bosonize.A08.wordDagger (dualOscWord w) := by
    induction w with
    | nil => rfl
    | cons g gs ih =>
        simp only [Bosonize.A08.wordDagger, List.map_cons, List.reverse_cons]
        change dualOscWord (Bosonize.A08.wordDagger gs ++ [(!g.1, g.2)]) =
          Bosonize.A08.wordDagger (dualOscGen g :: dualOscWord gs)
        rw [happend, ih]
        change Bosonize.A08.wordDagger (dualOscWord gs) ++
            [dualOscGen (!g.1, g.2)] =
          Bosonize.A08.wordDagger (dualOscGen g :: dualOscWord gs)
        rw [hgen]
        simp [Bosonize.A08.wordDagger]
  have hsign (w : Bosonize.A08.OscWord M) :
      dualOscWordSign (Bosonize.A08.wordDagger w) = star (dualOscWordSign w) := by
    induction w with
    | nil => simp [Bosonize.A08.wordDagger, dualOscWordSign]
    | cons g gs ih =>
        simp only [Bosonize.A08.wordDagger, List.map_cons, List.reverse_cons]
        change dualOscWordSign (Bosonize.A08.wordDagger gs ++ [(!g.1, g.2)]) =
          star (dualOscSign g * dualOscWordSign gs)
        rw [hsignAppend, ih]
        simp only [dualOscWordSign, mul_one]
        change star (dualOscWordSign gs) * dualOscSign (!g.1, g.2) =
          star (dualOscSign g * dualOscWordSign gs)
        rw [hgensign, star_mul]
  have hdualzero : dualOscSyntax (0 : OscSyntax M) = 0 := by simp [dualOscSyntax]
  have hdualadd (x y : OscSyntax M) :
      dualOscSyntax (x + y) = dualOscSyntax x + dualOscSyntax y := by
    simp only [dualOscSyntax, MonoidAlgebra.coeff_add]
    rw [Finsupp.sum_add_index' (by intro w; simp)
      (by intro w z t; simp [mul_add, Finsupp.single_add])]
    exact MonoidAlgebra.ofCoeff_add _ _
  have hdualsingle (w : Bosonize.A08.OscWord M) (z : ℂ) :
      dualOscSyntax (MonoidAlgebra.single w z) =
        MonoidAlgebra.single (dualOscWord w) (dualOscWordSign w * z) := by
    simp [dualOscSyntax]
  induction a using MonoidAlgebra.induction_linear with
  | zero =>
      calc
        dualOscSyntax (oscSyntaxDagger 0) = dualOscSyntax 0 :=
          congrArg dualOscSyntax (hzero 0)
        _ = 0 := hdualzero
        _ = oscSyntaxDagger 0 := (hzero 0).symm
        _ = oscSyntaxDagger (dualOscSyntax 0) := congrArg oscSyntaxDagger hdualzero.symm
  | add x y hx hy =>
      calc
        dualOscSyntax (oscSyntaxDagger (x + y)) =
            dualOscSyntax (oscSyntaxDagger x + oscSyntaxDagger y) :=
              congrArg dualOscSyntax (hadd x y)
        _ = dualOscSyntax (oscSyntaxDagger x) + dualOscSyntax (oscSyntaxDagger y) :=
              hdualadd _ _
        _ = oscSyntaxDagger (dualOscSyntax x) + oscSyntaxDagger (dualOscSyntax y) := by rw [hx, hy]
        _ = oscSyntaxDagger (dualOscSyntax x + dualOscSyntax y) := (hadd _ _).symm
        _ = oscSyntaxDagger (dualOscSyntax (x + y)) := congrArg oscSyntaxDagger (hdualadd x y).symm
  | single w z =>
      simp only [hsingle, hdualsingle]
      rw [hword, hsign]
      congr 1
      rw [star_mul]
      ring

theorem dualOscSyntax_involutive_contract {M : ℕ} (a : OscSyntax M) :
    dualOscSyntax (dualOscSyntax a) = a := by
  classical
  have hzero : dualOscSyntax (0 : OscSyntax M) = 0 := by simp [dualOscSyntax]
  have hadd (x y : OscSyntax M) :
      dualOscSyntax (x + y) = dualOscSyntax x + dualOscSyntax y := by
    simp only [dualOscSyntax, MonoidAlgebra.coeff_add]
    rw [Finsupp.sum_add_index' (by intro w; simp)
      (by intro w z t; simp [mul_add, Finsupp.single_add])]
    exact MonoidAlgebra.ofCoeff_add _ _
  have hsingle (w : Bosonize.A08.OscWord M) (z : ℂ) :
      dualOscSyntax (MonoidAlgebra.single w z) =
        MonoidAlgebra.single (dualOscWord w) (dualOscWordSign w * z) := by
    simp [dualOscSyntax]
  have hgen (g : Bosonize.A08.OscGen M) : dualOscGen (dualOscGen g) = g := by
    rcases g with ⟨b, ⟨ν, m⟩⟩
    cases b <;> cases ν <;> rfl
  have hword (w : Bosonize.A08.OscWord M) : dualOscWord (dualOscWord w) = w := by
    induction w with
    | nil => rfl
    | cons g gs ih => simp [dualOscWord, hgen, ih]
  have hsignGen (g : Bosonize.A08.OscGen M) :
      dualOscSign (dualOscGen g) * dualOscSign g = 1 := by
    by_cases hg : g.2.1 == Bosonize.A06.Orientation.right <;>
      simp [dualOscSign, dualOscGen, hg]
  have hsign (w : Bosonize.A08.OscWord M) :
      dualOscWordSign (dualOscWord w) * dualOscWordSign w = 1 := by
    induction w with
    | nil => simp [dualOscWord, dualOscWordSign]
    | cons g gs ih =>
        simp only [dualOscWord, dualOscWordSign]
        calc
          (dualOscSign (dualOscGen g) * dualOscWordSign (dualOscWord gs)) *
              (dualOscSign g * dualOscWordSign gs) =
              (dualOscSign (dualOscGen g) * dualOscSign g) *
                (dualOscWordSign (dualOscWord gs) * dualOscWordSign gs) := by ring
          _ = 1 := by rw [hsignGen, ih]; simp
  induction a using MonoidAlgebra.induction_linear with
  | zero =>
      calc
        dualOscSyntax (dualOscSyntax 0) = dualOscSyntax 0 := congrArg dualOscSyntax hzero
        _ = 0 := hzero
  | add x y hx hy =>
      calc
        dualOscSyntax (dualOscSyntax (x + y)) =
            dualOscSyntax (dualOscSyntax x + dualOscSyntax y) :=
              congrArg dualOscSyntax (hadd x y)
        _ = dualOscSyntax (dualOscSyntax x) + dualOscSyntax (dualOscSyntax y) := hadd _ _
        _ = x + y := by rw [hx, hy]
  | single w z =>
      rw [hsingle, hsingle, hword]
      congr 1
      rw [← mul_assoc, hsign]
      simp

theorem oscillatorParityAlgHom_one {M : ℕ} :
    oscillatorParityAlgHom (1 : Bosonize.A08.OscPoly M) = 1 := by
  simp [oscillatorParityAlgHom]

theorem oscillatorParityAlgHom_involutive {M : ℕ}
    (p : Bosonize.A08.OscPoly M) :
    oscillatorParityAlgHom (oscillatorParityAlgHom p) = p := by
  classical
  have hX (i : Bosonize.A08.OscMode M) :
      oscillatorParityAlgHom (MvPolynomial.X i) =
        (if i.1 = Bosonize.A06.Orientation.right then (-1 : ℂ) else 1) •
          MvPolynomial.X i := by
    simp [oscillatorParityAlgHom, MvPolynomial.aeval_X, MvPolynomial.smul_eq_C_mul]
  induction p using MvPolynomial.induction_on with
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
      calc
        oscillatorParityAlgHom (oscillatorParityAlgHom (p * MvPolynomial.X i)) =
            oscillatorParityAlgHom (oscillatorParityAlgHom p * oscillatorParityAlgHom (MvPolynomial.X i)) := by
              rw [map_mul oscillatorParityAlgHom p (MvPolynomial.X i)]
        _ = oscillatorParityAlgHom (oscillatorParityAlgHom p) *
            oscillatorParityAlgHom (oscillatorParityAlgHom (MvPolynomial.X i)) := by
              rw [map_mul oscillatorParityAlgHom (oscillatorParityAlgHom p)
                (oscillatorParityAlgHom (MvPolynomial.X i))]
        _ = p * MvPolynomial.X i := by
              rw [hp, hX]
              rw [map_smul oscillatorParityAlgHom
                (if i.1 = Bosonize.A06.Orientation.right then (-1 : ℂ) else 1)]
              rw [hX]
              by_cases hi : i.1 = Bosonize.A06.Orientation.right <;> simp [hi]
  | C r => simp [oscillatorParityAlgHom]

theorem oscillatorParityAlgHom_creation {M : ℕ} (ν : Bosonize.A06.Orientation)
    (m : Fin M) :
    oscillatorParityAlgHom (MvPolynomial.X (ν, m)) =
      (if ν = Bosonize.A06.Orientation.right then -1 else 1) •
        MvPolynomial.X (ν, m) := by
  simp [oscillatorParityAlgHom, MvPolynomial.smul_eq_C_mul]

theorem oscillatorDuality_generator {M : ℕ} (g : Bosonize.A08.OscGen M) :
    oscillatorDualityAlgHom (FreeAlgebra.ι ℂ g) =
      dualOscSign g • FreeAlgebra.ι ℂ (dualOscGen g) := by
  simp [oscillatorDualityAlgHom]

theorem oscillatorDuality_syntax_compatibility_contract {M : ℕ}
    (a : Bosonize.A08.OscAlgebra M) :
    oscFreeToSyntax M (oscillatorDualityAlgHom a) =
      dualOscSyntax (oscFreeToSyntax M a) := by
  classical
  have hadd (x y : OscSyntax M) :
      dualOscSyntax (x + y) = dualOscSyntax x + dualOscSyntax y := by
    simp only [dualOscSyntax, MonoidAlgebra.coeff_add]
    rw [Finsupp.sum_add_index' (by intro w; simp)
      (by intro w z t; simp [mul_add, Finsupp.single_add])]
    exact MonoidAlgebra.ofCoeff_add _ _
  have hsingle (w : Bosonize.A08.OscWord M) (z : ℂ) :
      dualOscSyntax (MonoidAlgebra.single w z) =
        MonoidAlgebra.single (dualOscWord w) (dualOscWordSign w * z) := by
    simp [dualOscSyntax]
  let Dsyn : OscSyntax M →ₐ[ℂ] OscSyntax M :=
    { toFun := dualOscSyntax
      map_zero' := by simp [dualOscSyntax]
      map_add' := hadd
      map_one' := dualOscSyntax_preserves_one_contract
      map_mul' := dualOscSyntax_preserves_mul_contract
      commutes' := by
        intro z
        change dualOscSyntax (MonoidAlgebra.single [] z) = MonoidAlgebra.single [] z
        simp [hsingle, dualOscWord, dualOscWordSign] }
  have h : (oscFreeToSyntax M).comp oscillatorDualityAlgHom =
      Dsyn.comp (oscFreeToSyntax M) := by
    apply FreeAlgebra.hom_ext
    funext g
    change oscFreeToSyntax M (oscillatorDualityAlgHom (FreeAlgebra.ι ℂ g)) =
      dualOscSyntax (oscFreeToSyntax M (FreeAlgebra.ι ℂ g))
    rw [oscillatorDuality_generator, map_smul]
    simp [oscFreeToSyntax, hsingle, dualOscWord, dualOscWordSign,
      MonoidAlgebra.smul_single, smul_eq_mul]
  exact AlgHom.congr_fun h a

theorem oscillator_bogoliubov_intertwining_contract {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (a : Bosonize.A08.OscAlgebra M) :
    oscillatorDualityAlgHom
      (Bosonize.A08.bogoliubovMap M P.c (-P.s) a) =
    Bosonize.A08.bogoliubovMap M (reflectHyperbolic P).c
      (-(reflectHyperbolic P).s)
      (oscillatorDualityAlgHom a) := by
  let D := oscillatorDualityAlgHom (M := M)
  let B := Bosonize.A08.bogoliubovMap M P.c (-P.s)
  let Bstar := Bosonize.A08.bogoliubovMap M P.c P.s
  have h : (D.comp B) = Bstar.comp D := by
    apply AlgHom.ext
    intro x
    induction x using FreeAlgebra.induction with
    | grade0 z => simp [D, B, Bstar]
    | grade1 g =>
        rcases g with ⟨b, ν, i⟩
        change D (Bosonize.A08.bogoliubovMap M P.c (-P.s)
            (FreeAlgebra.ι ℂ (b, ν, i))) =
          Bosonize.A08.bogoliubovMap M P.c P.s
            (D (FreeAlgebra.ι ℂ (b, ν, i)))
        simp only [Bosonize.A08.bogoliubovMap, FreeAlgebra.lift_ι_apply,
          map_add, AlgHom.map_smul_of_tower]
        rw [oscillatorDuality_generator, oscillatorDuality_generator]
        cases ν <;> simp [dualOscSign, dualOscGen,
          Bosonize.A07Interactions.oppositeOrientation] <;> module
    | mul x y hx hy => simp [map_mul, hx, hy]
    | add x y hx hy => simp [map_add, hx, hy]
  simpa [D, B, Bstar, reflectHyperbolic] using
    congrArg (fun f : Bosonize.A08.OscAlgebra M →ₐ[ℂ]
      Bosonize.A08.OscAlgebra M => f a) h

theorem dressed_right_generator_duality {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (m : Fin M) :
    oscillatorDualityAlgHom
      (Bosonize.V1S1.dressedLinearElement P.c P.s
        (Finsupp.single (true, (Bosonize.A06.Orientation.right, m)) 1)) =
      -Bosonize.V1S1.dressedLinearElement P.c (-P.s)
        (Finsupp.single (true, (Bosonize.A06.Orientation.right, m)) 1) := by
  let g : Bosonize.A08.OscGen M := (true, Bosonize.A06.Orientation.right, m)
  have hlin : Bosonize.V1S1.linearElement (Finsupp.single g (1 : ℂ)) =
      FreeAlgebra.ι ℂ g := by
    simp [Bosonize.V1S1.linearElement]
  have h := oscillator_bogoliubov_intertwining_contract (reflectHyperbolic P)
    (FreeAlgebra.ι ℂ g)
  rw [oscillatorDuality_generator] at h
  calc
    oscillatorDualityAlgHom (Bosonize.V1S1.dressedLinearElement P.c P.s
        (Finsupp.single g 1)) =
        oscillatorDualityAlgHom (Bosonize.A08.bogoliubovMap M P.c P.s
          (Bosonize.V1S1.linearElement (Finsupp.single g 1))) := by
      rw [Bosonize.V1S1.bare_to_dressed_conversion M P]
    _ = -Bosonize.A08.bogoliubovMap M P.c (-P.s) (FreeAlgebra.ι ℂ g) := by
      rw [hlin]
      simpa [reflectHyperbolic, g, dualOscGen, dualOscSign] using h
    _ = -Bosonize.V1S1.dressedLinearElement P.c (-P.s)
          (Finsupp.single g 1) := by
      simpa [reflectHyperbolic, hlin] using
        Bosonize.V1S1.bare_to_dressed_conversion M (reflectHyperbolic P)
          (Finsupp.single g 1)

theorem dressed_left_generator_duality {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (m : Fin M) :
    oscillatorDualityAlgHom
      (Bosonize.V1S1.dressedLinearElement P.c P.s
        (Finsupp.single (true, (Bosonize.A06.Orientation.left, m)) 1)) =
      Bosonize.V1S1.dressedLinearElement P.c (-P.s)
        (Finsupp.single (true, (Bosonize.A06.Orientation.left, m)) 1) := by
  let g : Bosonize.A08.OscGen M := (true, Bosonize.A06.Orientation.left, m)
  have hlin : Bosonize.V1S1.linearElement (Finsupp.single g (1 : ℂ)) =
      FreeAlgebra.ι ℂ g := by
    simp [Bosonize.V1S1.linearElement]
  have h := oscillator_bogoliubov_intertwining_contract (reflectHyperbolic P)
    (FreeAlgebra.ι ℂ g)
  rw [oscillatorDuality_generator] at h
  calc
    oscillatorDualityAlgHom (Bosonize.V1S1.dressedLinearElement P.c P.s
        (Finsupp.single g 1)) =
        oscillatorDualityAlgHom (Bosonize.A08.bogoliubovMap M P.c P.s
          (Bosonize.V1S1.linearElement (Finsupp.single g 1))) := by
      rw [Bosonize.V1S1.bare_to_dressed_conversion M P]
    _ = Bosonize.A08.bogoliubovMap M P.c (-P.s) (FreeAlgebra.ι ℂ g) := by
      rw [hlin]
      simpa [reflectHyperbolic, g, dualOscGen, dualOscSign] using h
    _ = Bosonize.V1S1.dressedLinearElement P.c (-P.s)
          (Finsupp.single g 1) := by
      simpa [reflectHyperbolic, hlin] using
        Bosonize.V1S1.bare_to_dressed_conversion M (reflectHyperbolic P)
          (Finsupp.single g 1)

theorem jointReflectionLinear_involutive {M : ℕ} (v : JointCarrier M) :
    jointReflectionLinear (jointReflectionLinear v) = v := by
  have hc (u : ChargeVec) : chargeReflectionLinear (chargeReflectionLinear u) = u := by
    classical
    ext N
    simp [chargeReflectionLinear, reflectChargeEquiv, Finsupp.domCongr_apply,
      reflectCharge_involutive]
  induction v using TensorProduct.inductionOn with
  | tmul a b => simp [jointReflectionLinear, hc, oscillatorParityAlgHom_involutive]
  | add a b ha hb =>
      change jointReflectionLinear (jointReflectionLinear (a + b)) = a + b
      rw [map_add, map_add, ha, hb]

theorem reflectChargeWord_preserves_comp_contract (a b : ChargeWord) :
    reflectChargeWord (ChargeWord.comp a b) =
      ChargeWord.comp (reflectChargeWord a) (reflectChargeWord b) := by
  apply congrArg₂ (fun t f => ({ target := t, amplitude := f } : ChargeWord))
  · apply Equiv.ext
    intro N
    change reflectCharge (a.target (b.target (reflectCharge N))) =
      reflectCharge (a.target (reflectCharge (reflectCharge (b.target (reflectCharge N)))))
    rw [reflectCharge_involutive]
  · funext N
    simp [reflectChargeWord, ChargeWord.comp, reflectCharge_involutive,
      Equiv.trans_apply]

theorem reflectChargeWord_basis_action (w : ChargeWord) (N : Charge) :
    chargeWordAction (reflectChargeWord w)
        (Finsupp.single N (1 : ℂ)) =
      chargeReflectionLinear
        (chargeWordAction w (Finsupp.single (reflectCharge N) 1)) := by
  rw [chargeWordAction_basis_contract, chargeWordAction_basis_contract]
  rw [map_smul, chargeReflectionLinear_basis]
  rfl

theorem reflectChargeWord_diagonal_observable (f : Charge → ℂ) :
    reflectChargeWord ⟨Equiv.refl Charge, f⟩ =
      ⟨Equiv.refl Charge, fun N => f (reflectCharge N)⟩ := by
  apply congrArg₂ (fun t amp => ({ target := t, amplitude := amp } : ChargeWord))
  · apply Equiv.ext
    intro N
    simp [reflectChargeWord, reflectCharge_involutive]
  · rfl

theorem reflectChargeWord_preserves_adjoint_contract (a : ChargeWord) :
    reflectChargeWord (ChargeWord.adjoint a) =
      ChargeWord.adjoint (reflectChargeWord a) := by
  apply congrArg₂ (fun t f => ({ target := t, amplitude := f } : ChargeWord))
  · apply Equiv.ext
    intro N
    simp [reflectChargeWord, ChargeWord.adjoint, reflectCharge_involutive]
  · funext N
    simp [reflectChargeWord, ChargeWord.adjoint, reflectCharge_involutive]

theorem dualCoeff_preserves_mul_contract {M : ℕ} (a b : vertexCoeff M) :
    dualCoeff (vertexCoeffMul a b) = vertexCoeffMul (dualCoeff a) (dualCoeff b) := by
  rcases a with ⟨a, x⟩
  rcases b with ⟨b, y⟩
  simp [dualCoeff, vertexCoeffMul, reflectChargeWord_preserves_comp_contract,
    dualOscSyntax_preserves_mul_contract]
  rfl

theorem dualCoeff_preserves_adjoint_contract {M : ℕ} (a : vertexCoeff M) :
    dualCoeff (vertexCoeffAdjoint a) = vertexCoeffAdjoint (dualCoeff a) := by
  rcases a with ⟨a, x⟩
  simp [dualCoeff, vertexCoeffAdjoint,
    reflectChargeWord_preserves_adjoint_contract,
    dualOscSyntax_preserves_dagger_contract]
  rfl

theorem dualCoeff_involutive_contract {M : ℕ} (a : vertexCoeff M) :
    dualCoeff (dualCoeff a) = a := by
  rcases a with ⟨w, x⟩
  apply congrArg₂ (fun q y => (q, y))
  · apply congrArg₂ (fun t f => ({ target := t, amplitude := f } : ChargeWord))
    · apply Equiv.ext
      intro N
      simp [dualCoeff, reflectChargeWord, reflectCharge_involutive]
    · funext N
      simp [dualCoeff, reflectChargeWord, reflectCharge_involutive]
  · exact dualOscSyntax_involutive_contract x

theorem D_P_scalar_contract {M : ℕ} (P : Bosonize.Ch18.HyperbolicPair)
    (z : ℂ) (a : vertexCoeff M) :
    D_P P (vertexCoeffScale z a) = vertexCoeffScale z (D_P P a) := by
  rcases a with ⟨w, x⟩
  rfl

theorem D_P_unit_contract {M : ℕ} (P : Bosonize.Ch18.HyperbolicPair) :
    D_P (M := M) P vertexCoeffOne = vertexCoeffOne := by
  change (reflectChargeWord ⟨Equiv.refl Charge, fun _ => (1 : ℂ)⟩,
      dualOscSyntax (1 : OscSyntax M)) = vertexCoeffOne
  rw [dualOscSyntax_preserves_one_contract, reflectChargeWord_diagonal_observable]
  rfl

theorem D_twice_typed_contract {M : ℕ} (P : Bosonize.Ch18.HyperbolicPair)
    (a : vertexCoeff M) :
    D_P (reflectHyperbolic P) (D_P P a) = a := by
  exact dualCoeff_involutive_contract a

theorem represented_action_intertwining_contract {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (a : vertexCoeff M) :
    jointCoeffAction (reflectHyperbolic P) (dualCoeff a) =
      (jointReflectionLinear.comp (jointCoeffAction P a)).comp
        jointReflectionLinear := by
  classical
  have hderiv (i : Bosonize.A08.OscMode M) (p : Bosonize.A08.OscPoly M) :
      MvPolynomial.pderiv i (oscillatorParityAlgHom p) =
        (if i.1 = Bosonize.A06.Orientation.right then (-1 : ℂ) else 1) •
          oscillatorParityAlgHom (MvPolynomial.pderiv i p) := by
    classical
    let s (j : Bosonize.A08.OscMode M) : ℂ :=
      if j.1 = Bosonize.A06.Orientation.right then -1 else 1
    have hX (j : Bosonize.A08.OscMode M) :
        oscillatorParityAlgHom (MvPolynomial.X j) = s j • MvPolynomial.X j := by
      simp [oscillatorParityAlgHom, s]
    change MvPolynomial.pderiv i (oscillatorParityAlgHom p) =
      s i • oscillatorParityAlgHom (MvPolynomial.pderiv i p)
    induction p using MvPolynomial.induction_on with
    | C z => simp [oscillatorParityAlgHom]
    | add p q hp hq => simp [map_add, hp, hq, smul_add]
    | mul_X p j hp =>
      simp only [map_mul, hX, MvPolynomial.pderiv_mul, map_add, hp]
      by_cases hij : i = j
      · subst j
        simp [smul_add]
      · simp [MvPolynomial.pderiv_X_of_ne (Ne.symm hij), smul_smul, mul_comm]
  have hrep (a : Bosonize.A08.OscAlgebra M)
      (p : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscRep M (oscillatorDualityAlgHom a) (oscillatorParityAlgHom p) =
        oscillatorParityAlgHom (Bosonize.A08.oscRep M a p) := by
    induction a using FreeAlgebra.induction generalizing p with
    | grade0 z => simp
    | grade1 g =>
      rcases g with ⟨b, ν, m⟩
      rw [oscillatorDuality_generator]
      cases b
      · cases ν <;>
          simp [dualOscSign, dualOscGen, Bosonize.A08.oscRep,
            Bosonize.A08.oscAnnihilation, hderiv]
      · cases ν <;>
          simp [dualOscSign, dualOscGen, Bosonize.A08.oscRep,
            Bosonize.A08.oscCreation, map_mul, oscillatorParityAlgHom_creation]
    | add x y hx hy => simp [map_add, hx, hy]
    | mul x y hx hy => simp [map_mul, Module.End.mul_apply, hx, hy]
  have heval (a : OscSyntax M) :
      oscSyntaxEval (dualOscSyntax a) = oscillatorDualityAlgHom (oscSyntaxEval a) := by
    classical
    have eadd (x y : OscSyntax M) : oscSyntaxEval (x + y) = oscSyntaxEval x + oscSyntaxEval y := by
      simp only [oscSyntaxEval, MonoidAlgebra.coeff_add]
      exact Finsupp.sum_add_index' (by intro w; simp) (by intro w z t; simp [add_smul])
    have hword (w : Bosonize.A08.OscWord M) :
        oscFreeToSyntax M (Bosonize.A08.wordElement M w) = MonoidAlgebra.single w (1 : ℂ) := by
      induction w with
      | nil => simp [Bosonize.A08.wordElement, MonoidAlgebra.one_def]; rfl
      | cons g w ih =>
        change oscFreeToSyntax M (FreeAlgebra.ι ℂ g * Bosonize.A08.wordElement M w) = _
        rw [map_mul, ih]
        simp only [oscFreeToSyntax, FreeAlgebra.lift_ι_apply]
        rw [MonoidAlgebra.single_mul_single, one_mul]
        rfl
    have hround (x : OscSyntax M) : oscFreeToSyntax M (oscSyntaxEval x) = x := by
      induction x using MonoidAlgebra.induction_linear with
      | zero => simp [oscSyntaxEval]
      | add x y hx hy => rw [eadd, map_add, hx, hy]
      | single w z =>
        simp [oscSyntaxEval, map_smul, hword, MonoidAlgebra.smul_single, smul_eq_mul]
    have h := congrArg oscSyntaxEval
      (oscillatorDuality_syntax_compatibility_contract (oscSyntaxEval a))
    simpa only [oscSyntax_roundtrip_freeAlgebra_contract, hround] using h.symm
  classical
  have hc (w : ChargeWord) (v : ChargeVec) :
      chargeWordActionLinear (reflectChargeWord w) v =
        chargeReflectionLinear (chargeWordActionLinear w (chargeReflectionLinear v)) := by
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v u hv hu => simp [hv, hu]
    | single N z =>
      have hz : Finsupp.single N z = z • Finsupp.single N (1 : ℂ) := by simp
      rw [hz]
      simp only [map_smul]
      congr 1
      rw [chargeReflectionLinear_basis]
      exact reflectChargeWord_basis_action w N
  have ho (x : OscSyntax M) (p : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscRep M
          (Bosonize.A08.bogoliubovMap M (reflectHyperbolic P).c
            (-(reflectHyperbolic P).s) (oscSyntaxEval (dualOscSyntax x))) p =
        oscillatorParityAlgHom (Bosonize.A08.oscRep M
          (Bosonize.A08.bogoliubovMap M P.c (-P.s) (oscSyntaxEval x))
          (oscillatorParityAlgHom p)) := by
    rw [heval, ← oscillator_bogoliubov_intertwining_contract]
    simpa only [oscillatorParityAlgHom_involutive] using
      hrep
        (Bosonize.A08.bogoliubovMap M P.c (-P.s) (oscSyntaxEval x))
        (oscillatorParityAlgHom p)
  apply TensorProduct.ext'
  intro v p
  simp only [jointCoeffAction, dualCoeff, jointReflectionLinear,
    LinearMap.comp_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply]
  rw [hc, ho]

theorem represented_action_kernel_transport_contract {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (a : vertexCoeff M) :
    jointCoeffAction P a = 0 ↔
      jointCoeffAction (reflectHyperbolic P) (dualCoeff a) = 0 := by
  constructor
  · intro h
    rw [represented_action_intertwining_contract, h]
    simp
  · intro h
    have hi := represented_action_intertwining_contract (reflectHyperbolic P) (dualCoeff a)
    rw [reflectHyperbolic_involutive, dualCoeff_involutive_contract] at hi
    rw [hi, h]
    simp

theorem representedSeries_intertwining_contract {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (A : VertexSeries M) (n : ℕ) :
    representedSeries (reflectHyperbolic P) (dualSeries A) n =
      (jointReflectionLinear.comp (representedSeries P A n)).comp
        jointReflectionLinear := by
  have h (m : Multiset (vertexCoeff M)) :
      vertexMultisetAction (reflectHyperbolic P) (m.map dualCoeff) =
        (jointReflectionLinear.comp (vertexMultisetAction P m)).comp
          jointReflectionLinear := by
    induction m using Multiset.induction_on with
    | empty => simp [vertexMultisetAction]
    | cons a m ih =>
      simp only [vertexMultisetAction, Multiset.map_cons, Multiset.sum_cons,
        LinearMap.add_comp, LinearMap.comp_add] at ih ⊢
      rw [represented_action_intertwining_contract, ih]
  exact h (A n)

theorem representedSeries_mul_contract {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (A B : VertexSeries M) :
    representedSeries P (vertexSeriesMul A B) =
      representedSeriesMul (representedSeries P A) (representedSeries P B) := by
  let F : Multiset (vertexCoeff M) →+ Module.End ℂ (JointCarrier M) :=
    { toFun := vertexMultisetAction P
      map_zero' := by simp [vertexMultisetAction]
      map_add' := by intro x y; simp [vertexMultisetAction] }
  have hcons (a : vertexCoeff M) (s : Multiset (vertexCoeff M)) :
      F (a ::ₘ s) = jointCoeffAction P a + F s := by
    change vertexMultisetAction P (a ::ₘ s) = jointCoeffAction P a + vertexMultisetAction P s
    simp [vertexMultisetAction]
  have hleft (a : vertexCoeff M) (t : Multiset (vertexCoeff M)) :
      F (t.map (vertexCoeffMul a)) = (jointCoeffAction P a).comp (F t) := by
    induction t using Multiset.induction_on with
    | empty => simp [F]
    | cons b t ih =>
      simp only [Multiset.map_cons, hcons]
      rw [LinearMap.comp_add, jointCoeffAction_mul_contract, ih]
  have hmul (s t : Multiset (vertexCoeff M)) :
      F (s.bind fun a => t.map (vertexCoeffMul a)) = (F s).comp (F t) := by
    induction s using Multiset.induction_on with
    | empty => simp [F]
    | cons a s ih =>
      rw [Multiset.cons_bind, map_add, hleft, ih]
      rw [hcons, LinearMap.add_comp]
  funext n
  change F (∑ k ∈ Finset.range (n + 1), (A k).bind
    fun a => (B (n-k)).map (vertexCoeffMul a)) =
      ∑ k ∈ Finset.range (n+1), (F (A k)).comp (F (B (n-k)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact hmul _ _

theorem joint_functional_transport_from_action {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (N : Charge) (a : vertexCoeff M) :
    jointCoeffFunctional (reflectHyperbolic P) (reflectCharge N) (dualCoeff a) =
      jointCoeffFunctional P N a := by
  classical
  have hpoly (p : Bosonize.A08.OscPoly M) :
      MvPolynomial.constantCoeff (oscillatorParityAlgHom p) =
        MvPolynomial.constantCoeff p := by
    induction p using MvPolynomial.induction_on with
    | C z => simp [oscillatorParityAlgHom]
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp =>
      rcases i with ⟨ν, m⟩
      cases ν <;> simp [map_mul, oscillatorParityAlgHom_creation]
  have hf (v : JointCarrier M) :
      jointTensorFunctional (reflectHyperbolic P) (reflectCharge N)
          (jointReflectionLinear v) = jointTensorFunctional P N v := by
    induction v using TensorProduct.inductionOn with
    | tmul v p =>
      simp only [jointReflectionLinear, TensorProduct.map_tmul,
        jointTensorFunctional_tmul, AlgHom.toLinearMap_apply]
      change chargeReflectionLinear v (reflectCharge N) *
        MvPolynomial.constantCoeff (oscillatorParityAlgHom p) =
          v N * MvPolynomial.constantCoeff p
      rw [hpoly]
      simp [chargeReflectionLinear, reflectChargeEquiv, Finsupp.domCongr_apply,
        reflectCharge_involutive]
    | add x y hx hy => simp [hx, hy]
  have hb : jointReflectionLinear (jointBasis M (reflectCharge N)) = jointBasis M N := by
    simp [jointReflectionLinear, jointBasis, chargeReflectionLinear_basis,
      oscillatorParityAlgHom_one, reflectCharge_involutive]
  unfold jointCoeffFunctional
  rw [represented_action_intertwining_contract]
  simp only [LinearMap.comp_apply, hb]
  exact hf _

theorem dualSeries_product_contract {M : ℕ} (A B : VertexSeries M) :
    dualSeries (vertexSeriesMul A B) =
      vertexSeriesMul (dualSeries A) (dualSeries B) := by
  funext n
  simp only [dualSeries, vertexSeriesMul]
  rw [← Multiset.mapAddMonoidHom_apply]
  rw [map_sum (Multiset.mapAddMonoidHom dualCoeff)]
  simp only [Multiset.mapAddMonoidHom_apply, Multiset.map_bind]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Multiset.bind_map]
  apply Multiset.bind_congr
  intro a ha
  rw [Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro b hb
  exact dualCoeff_preserves_mul_contract a b

theorem dualSeries_adjoint_contract {M : ℕ} (A : VertexSeries M) :
    dualSeries (vertexSeriesAdjoint A) =
      vertexSeriesAdjoint (dualSeries A) := by
  funext n
  simp only [dualSeries, vertexSeriesAdjoint, Multiset.map_map, Function.comp_def]
  apply Multiset.map_congr rfl
  intro a ha
  exact dualCoeff_preserves_adjoint_contract a

theorem dualSeries_involutive_contract {M : ℕ} (A : VertexSeries M) :
    dualSeries (dualSeries A) = A := by
  funext n
  simp [dualSeries, Multiset.map_map, Function.comp_def,
    dualCoeff_involutive_contract]

theorem canonicalKleinD_reflection_contract {L h : ℕ} (x : Position L) :
    reflectChargeWord (canonicalKleinD h L x) =
      ChargeWord.scale ((Bosonize.A01.canonicalRoot L) ^ (x.val : ℤ))
        (canonicalKleinSAdj h L x) := by
  have hg (h : ℕ) (N : Charge) :
      chargeGauge h (reflectCharge N) = (-1 : ℂ) ^ N.2 * chargeGauge h N := by
    have he : chargeGaugeExponent h (reflectCharge N) = chargeGaugeExponent h N + N.2 := by
      have hp : (-N.2) * (-N.2 - 1) = N.2 * (N.2 - 1) + 2 * N.2 := by ring
      unfold chargeGaugeExponent reflectCharge
      dsimp
      rw [hp]
      omega
    unfold chargeGauge
    rw [he, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), mul_comm]
  have hbare (x : Position L) :
      reflectChargeWord (kleinD L x) =
        ChargeWord.scale (-((Bosonize.A01.canonicalRoot L) ^ (x.val : ℤ)))
          (kleinSAdj L x) := by
    have hroot : star (Bosonize.A01.canonicalRoot L) = (Bosonize.A01.canonicalRoot L)⁻¹ := by
      unfold Bosonize.A01.canonicalRoot
      change (starRingEnd ℂ) (Complex.exp (2 * ↑Real.pi * Complex.I / (L : ℂ))) = _
      rw [← Complex.exp_neg, ← Complex.exp_conj]
      congr 1
      have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
      simp [htwo]
      ring
    have hn : Bosonize.A01.canonicalRoot L ≠ 0 := Complex.exp_ne_zero _
    apply congrArg₂ (fun t f => ({target := t, amplitude := f} : ChargeWord))
    · apply Equiv.ext
      intro N
      simp [kleinD, kleinSAdj, reflectCharge,
        chargeShiftDEquiv, chargeShiftSEquiv, chargeShiftD, inverseShiftS, add_comm]
    · funext N
      simp [kleinD, kleinSAdj, kleinS,
        reflectCharge, inverseShiftS, chargePhase, Bosonize.A01.integerCharacter,
        aD, aS, star_mul, star_zpow₀, hroot,
        zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      simp only [← zpow_neg]
      rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ hn]
      have he : (x.val : ℤ) + -((N.1 + 1 + (N.2 + 1)) * (x.val : ℤ)) =
          (-N.2 - N.1 - 1) * (x.val : ℤ) := by ring
      rw [he, mul_comm]
  apply congrArg₂ (fun t f => ({target := t, amplitude := f} : ChargeWord))
  · apply Equiv.ext
    intro N
    simp [canonicalKleinD, canonicalKleinSAdj, reflectCharge,
      chargeShiftDEquiv, chargeShiftSEquiv, chargeShiftD, inverseShiftS, add_comm]
  · funext N
    have hb := congrFun (congrArg ChargeWord.amplitude (hbare x)) N
    change (kleinD L x).amplitude (reflectCharge N) =
      -((Bosonize.A01.canonicalRoot L) ^ (x.val : ℤ)) *
        star ((kleinS L x).amplitude (inverseShiftS N)) at hb
    change chargeGauge h (chargeShiftD (reflectCharge N)) *
      (kleinD L x).amplitude (reflectCharge N) * star (chargeGauge h (reflectCharge N)) =
        (Bosonize.A01.canonicalRoot L) ^ (x.val : ℤ) *
          star (chargeGauge h (chargeShiftS (inverseShiftS N)) *
            (kleinS L x).amplitude (inverseShiftS N) * star (chargeGauge h (inverseShiftS N)))
    have ht : chargeShiftD (reflectCharge N) = reflectCharge (inverseShiftS N) := by
      ext <;> simp [chargeShiftD, reflectCharge, inverseShiftS, add_comm, sub_eq_add_neg]
    have hi : chargeShiftS (inverseShiftS N) = N := by
      ext <;> simp [chargeShiftS, inverseShiftS]
    rw [ht, hg, hg, hb, hi,
      star_mul, star_mul, star_star]
    have hs : (-1 : ℂ) ^ N.2 * (-1 : ℂ) ^ N.2 = 1 := by
      rw [← mul_zpow]
      norm_num
    simp only [star_mul, star_zpow₀, star_neg, star_one, inverseShiftS,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]
    linear_combination (chargeGauge h ((N.1 + 1, N.2 + 1)) *
      (Bosonize.A01.canonicalRoot L) ^ (x.val : ℤ) *
      star ((kleinS L x).amplitude ((N.1 + 1, N.2 + 1))) * star (chargeGauge h N)) * hs

theorem canonicalKleinS_reflection_contract {L h : ℕ} (x : Position L) :
    reflectChargeWord (canonicalKleinS h L x) =
      ChargeWord.scale ((Bosonize.A01.canonicalRoot L) ^ (x.val : ℤ))
        (canonicalKleinDAdj h L x) := by
  have hg (h : ℕ) (N : Charge) :
      chargeGauge h (reflectCharge N) = (-1 : ℂ) ^ N.2 * chargeGauge h N := by
    have he : chargeGaugeExponent h (reflectCharge N) = chargeGaugeExponent h N + N.2 := by
      have hp : (-N.2) * (-N.2 - 1) = N.2 * (N.2 - 1) + 2 * N.2 := by ring
      unfold chargeGaugeExponent reflectCharge
      dsimp
      rw [hp]
      omega
    unfold chargeGauge
    rw [he, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), mul_comm]
  have hbare (x : Position L) :
      reflectChargeWord (kleinS L x) =
        ChargeWord.scale (-((Bosonize.A01.canonicalRoot L) ^ (x.val : ℤ)))
          (kleinDAdj L x) := by
    have hroot : star (Bosonize.A01.canonicalRoot L) = (Bosonize.A01.canonicalRoot L)⁻¹ := by
      unfold Bosonize.A01.canonicalRoot
      change (starRingEnd ℂ) (Complex.exp (2 * ↑Real.pi * Complex.I / (L : ℂ))) = _
      rw [← Complex.exp_neg, ← Complex.exp_conj]
      congr 1
      have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
      simp [htwo]
      ring
    have hn : Bosonize.A01.canonicalRoot L ≠ 0 := Complex.exp_ne_zero _
    apply congrArg₂ (fun t f => ({target := t, amplitude := f} : ChargeWord))
    · apply Equiv.ext
      intro N
      simp [kleinS, kleinDAdj, reflectCharge,
        chargeShiftSEquiv, chargeShiftDEquiv, chargeShiftS, inverseShiftD, add_comm]
    · funext N
      simp [kleinS, kleinDAdj, kleinD,
        reflectCharge, inverseShiftD, chargePhase, Bosonize.A01.integerCharacter,
        aD, aS, star_mul, star_zpow₀, hroot,
        zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      simp only [div_neg, div_one, mul_neg, neg_neg, ← zpow_neg]
      rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ hn]
      have he : (x.val : ℤ) + -((N.2 + 1 - (N.1 - 1) - 1) * (x.val : ℤ)) =
          (N.1 + -N.2) * (x.val : ℤ) := by ring
      rw [he, mul_comm]
  apply congrArg₂ (fun t f => ({target := t, amplitude := f} : ChargeWord))
  · apply Equiv.ext
    intro N
    simp [canonicalKleinS, canonicalKleinDAdj, reflectCharge,
      chargeShiftDEquiv, chargeShiftSEquiv, chargeShiftS, inverseShiftD, add_comm]
  · funext N
    have hb := congrFun (congrArg ChargeWord.amplitude (hbare x)) N
    change (kleinS L x).amplitude (reflectCharge N) =
      -((Bosonize.A01.canonicalRoot L) ^ (x.val : ℤ)) *
        star ((kleinD L x).amplitude (inverseShiftD N)) at hb
    change chargeGauge h (chargeShiftS (reflectCharge N)) *
      (kleinS L x).amplitude (reflectCharge N) * star (chargeGauge h (reflectCharge N)) =
        (Bosonize.A01.canonicalRoot L) ^ (x.val : ℤ) *
          star (chargeGauge h (chargeShiftD (inverseShiftD N)) *
            (kleinD L x).amplitude (inverseShiftD N) * star (chargeGauge h (inverseShiftD N)))
    have ht : chargeShiftS (reflectCharge N) = reflectCharge (inverseShiftD N) := by
      ext <;> simp [chargeShiftS, reflectCharge, inverseShiftD, add_comm, sub_eq_add_neg]
    have hi : chargeShiftD (inverseShiftD N) = N := by
      ext <;> simp [chargeShiftD, inverseShiftD]
    rw [ht, hg, hg, hb, hi,
      star_mul, star_mul, star_star]
    have hs : (-1 : ℂ) ^ N.2 * (-1 : ℂ) ^ N.2 = 1 := by
      rw [← mul_zpow]
      norm_num
    simp only [star_mul, star_zpow₀, star_neg, star_one, inverseShiftD,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]
    linear_combination (chargeGauge h ((N.1 - 1, N.2 + 1)) *
      (Bosonize.A01.canonicalRoot L) ^ (x.val : ℤ) *
      star ((kleinD L x).amplitude ((N.1 - 1, N.2 + 1))) * star (chargeGauge h N)) * hs

theorem simplifiedKleinD_reflection_sign_contract {L : ℕ} (x : Position L) :
    reflectChargeWord (kleinD L x) =
      ChargeWord.scale (-((Bosonize.A01.canonicalRoot L) ^ (x.val : ℤ)))
        (kleinSAdj L x) := by
  have hroot : star (Bosonize.A01.canonicalRoot L) = (Bosonize.A01.canonicalRoot L)⁻¹ := by
    unfold Bosonize.A01.canonicalRoot
    change (starRingEnd ℂ) (Complex.exp (2 * ↑Real.pi * Complex.I / (L : ℂ))) = _
    rw [← Complex.exp_neg, ← Complex.exp_conj]
    congr 1
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
    simp [htwo]
    ring
  have hn : Bosonize.A01.canonicalRoot L ≠ 0 := Complex.exp_ne_zero _
  apply congrArg₂ (fun t f => ({target := t, amplitude := f} : ChargeWord))
  · apply Equiv.ext
    intro N
    simp [kleinD, kleinSAdj, reflectCharge,
      chargeShiftDEquiv, chargeShiftSEquiv, chargeShiftD, inverseShiftS, add_comm]
  · funext N
    simp [kleinD, kleinSAdj, kleinS,
      reflectCharge, inverseShiftS, chargePhase, Bosonize.A01.integerCharacter,
      aD, aS, star_mul, star_zpow₀, hroot,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    simp only [← zpow_neg]
    rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ hn]
    have he : (x.val : ℤ) + -((N.1 + 1 + (N.2 + 1)) * (x.val : ℤ)) =
        (-N.2 - N.1 - 1) * (x.val : ℤ) := by ring
    rw [he, mul_comm]

theorem simplifiedKleinS_reflection_sign_contract {L : ℕ} (x : Position L) :
    reflectChargeWord (kleinS L x) =
      ChargeWord.scale (-((Bosonize.A01.canonicalRoot L) ^ (x.val : ℤ)))
        (kleinDAdj L x) := by
  have hroot : star (Bosonize.A01.canonicalRoot L) = (Bosonize.A01.canonicalRoot L)⁻¹ := by
    unfold Bosonize.A01.canonicalRoot
    change (starRingEnd ℂ) (Complex.exp (2 * ↑Real.pi * Complex.I / (L : ℂ))) = _
    rw [← Complex.exp_neg, ← Complex.exp_conj]
    congr 1
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
    simp [htwo]
    ring
  have hn : Bosonize.A01.canonicalRoot L ≠ 0 := Complex.exp_ne_zero _
  apply congrArg₂ (fun t f => ({target := t, amplitude := f} : ChargeWord))
  · apply Equiv.ext
    intro N
    simp [kleinS, kleinDAdj, reflectCharge,
      chargeShiftSEquiv, chargeShiftDEquiv, chargeShiftS, inverseShiftD, add_comm]
  · funext N
    simp [kleinS, kleinDAdj, kleinD,
      reflectCharge, inverseShiftD, chargePhase, Bosonize.A01.integerCharacter,
      aD, aS, star_mul, star_zpow₀, hroot,
      zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    simp only [div_neg, div_one, mul_neg, neg_neg, ← zpow_neg]
    rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ hn]
    have he : (x.val : ℤ) + -((N.2 + 1 - (N.1 - 1) - 1) * (x.val : ℤ)) =
        (N.1 + -N.2) * (x.val : ℤ) := by ring
    rw [he, mul_comm]

theorem canonical_degree_zero_D_action {h : ℕ} (N : Charge)
    (x : Position (2 * h)) :
    chargeWordAction (reflectChargeWord (canonicalKleinD h (2 * h) x))
        (Finsupp.single N (1 : ℂ)) =
      ((Bosonize.A01.canonicalRoot (2*h)) ^ (x.val : ℤ)) •
        chargeWordAction (canonicalKleinSAdj h (2 * h) x)
          (Finsupp.single N (1 : ℂ)) := by
  rw [canonicalKleinD_reflection_contract]
  simp [chargeWordAction_basis_contract, ChargeWord.scale, mul_smul]

theorem duality_charge_vector_contract (N : Charge) :
    reflectCharge (reflectCharge N) = N := reflectCharge_involutive N

theorem oscillator_field_D_duality {M L : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (x : Position L) :
    dualOscLinearForm (xDForm (M := M) (L := L) P x) =
      -xSForm (M := M) (L := L) (reflectHyperbolic P) x := by
  have hdiag (f : Bosonize.V1S1.OscLinearForm M)
      (g : Bosonize.A08.OscGen M) : dualOscLinearForm f g = dualOscSign g * f g := by
    classical
    have hg (k : Bosonize.A08.OscGen M) : dualOscGen k = k := by
      rcases k with ⟨b, ν, m⟩
      cases ν <;> rfl
    simp [dualOscLinearForm, hg, Finsupp.sum_apply, Finsupp.single_apply]
    intro h
    exact Or.inr h
  classical
  have hq (c s : ℝ) (x : Position L) (b : Bool)
    (ν μ : Bosonize.A06.Orientation) (i : Fin M) :
    qForm c s ν x (b, (μ, i)) =
      (if μ = ν then (c : ℂ) *
        (Bosonize.A01.canonicalRoot L) ^
          ((if b then -(epsilon ν) else epsilon ν) * ((i.val : ℤ) + 1) * (x.val : ℤ)) /
          ((i.val : ℂ) + 1) else 0) +
      (if μ = Bosonize.A07Interactions.oppositeOrientation ν then (s : ℂ) *
        (Bosonize.A01.canonicalRoot L) ^
          ((if b then epsilon ν else -(epsilon ν)) * ((i.val : ℤ) + 1) * (x.val : ℤ)) /
          ((i.val : ℂ) + 1) else 0) :=   by
    classical
    cases b <;> cases ν <;> cases μ <;>
      simp [qForm, dressedModeForm, Bosonize.V1S1.dressedGeneratorForm,
        epsilon, Bosonize.A07Interactions.oppositeOrientation, Finsupp.single_apply] <;> ring
  ext g
  rw [hdiag]
  rcases g with ⟨b, ν, m⟩
  cases b <;> cases ν <;>
    simp [xDForm, xSForm, hq, dualOscSign, reflectHyperbolic,
      epsilon, Bosonize.A07Interactions.oppositeOrientation] <;> ring

theorem oscillator_field_S_duality {M L : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (x : Position L) :
    dualOscLinearForm (xSForm (M := M) (L := L) P x) =
      -xDForm (M := M) (L := L) (reflectHyperbolic P) x := by
  have hdiag (f : Bosonize.V1S1.OscLinearForm M)
      (g : Bosonize.A08.OscGen M) : dualOscLinearForm f g = dualOscSign g * f g := by
    classical
    have hg (k : Bosonize.A08.OscGen M) : dualOscGen k = k := by
      rcases k with ⟨b, ν, m⟩
      cases ν <;> rfl
    simp [dualOscLinearForm, hg, Finsupp.sum_apply, Finsupp.single_apply]
    intro h
    exact Or.inr h
  ext g
  have hh := congrArg (fun f : Bosonize.V1S1.OscLinearForm M => f g)
    (oscillator_field_D_duality (reflectHyperbolic P) x)
  rw [reflectHyperbolic_involutive, hdiag] at hh
  rw [hdiag]
  rcases g with ⟨b, ν, m⟩
  cases ν <;> simp [dualOscSign] at hh ⊢ <;> simp [hh]

theorem chargeWord_reflection_source_first (w : ChargeWord) (N : Charge) :
    chargeWordAction (reflectChargeWord w) (Finsupp.single N (1 : ℂ)) =
      w.amplitude (reflectCharge N) •
        Finsupp.single (reflectCharge (w.target (reflectCharge N))) 1 := by
  rw [chargeWordAction_basis_contract]
  rfl

theorem chargeBasisExpectation_reflection (N : Charge) (w : ChargeWord) :
    chargeBasisExpectation (reflectCharge N) (reflectChargeWord w) =
      chargeBasisExpectation N w := by
  have hcond : reflectCharge (w.target N) = reflectCharge N ↔ w.target N = N := by
    constructor
    · intro h; exact reflectChargeEquiv.injective h
    · intro h
      simp [h]
  simp [chargeBasisExpectation, reflectChargeWord, reflectCharge_involutive, hcond]

theorem duality_vertex_D_contract {M h : ℕ} (hh : 0 < h)
    (P : Bosonize.Ch18.HyperbolicPair) (x : Position (2 * h)) :
    dualSeries (vertexWeyl (M := M) hh P x false) =
      (fun n => ((vertexWeylAdj (M := M) hh (reflectHyperbolic P) x true) n).map
        (vertexCoeffScale ((Bosonize.A01.canonicalRoot (2*h)) ^ (x.val : ℤ)))) := by
  sorry

theorem duality_vertex_S_contract {M h : ℕ} (hh : 0 < h)
    (P : Bosonize.Ch18.HyperbolicPair) (x : Position (2 * h)) :
    dualSeries (vertexWeyl (M := M) hh P x true) =
      (fun n => ((vertexWeylAdj (M := M) hh (reflectHyperbolic P) x false) n).map
        (vertexCoeffScale ((Bosonize.A01.canonicalRoot (2*h)) ^ (x.val : ℤ)))) := by
  sorry

theorem duality_vertex_D_t0_contract {M h : ℕ} (hh : 0 < h)
    (P : Bosonize.Ch18.HyperbolicPair) (x : Position (2 * h)) :
    (dualSeries (vertexWeyl (M := M) hh P x false)) 0 =
      (vertexSeriesScalarMul
        (fun n => if n = 0 then
          ((Bosonize.A01.canonicalRoot (2*h)) ^ (x.val : ℤ)) else 0)
        (vertexWeylAdj (M := M) hh (reflectHyperbolic P) x true)) 0 := by
  have he (Q : Bosonize.Ch18.HyperbolicPair) (b : Bool) :
      oscillatorExp (M := M) Q x b 0 = 1 := by
    simp [oscillatorExp, oscillatorExpWithScalar]
  have hd : oscSyntaxDagger (1 : OscSyntax M) = 1 := by
    rw [MonoidAlgebra.one_def]
    simp [oscSyntaxDagger, Bosonize.A08.wordDagger]
    rfl
  simp only [dualSeries, vertexWeyl, vertexWeylAdj, vertexSeriesAdjoint,
    vertexSeriesScalarMul, he, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, Nat.sub_self, ite_true]
  set_option backward.isDefEq.respectTransparency false in
    simp only [Multiset.map_singleton]
  change ({(reflectChargeWord (ChargeWord.scale (((2*h : ℕ) : ℂ)⁻¹)
    (canonicalKleinD h (2*h) x)), dualOscSyntax 1)} : Multiset (vertexCoeff M)) =
    {(ChargeWord.scale ((Bosonize.A01.canonicalRoot (2*h)) ^ (x.val : ℤ))
      (ChargeWord.adjoint (ChargeWord.scale (((2*h : ℕ) : ℂ)⁻¹)
        (canonicalKleinS h (2*h) x))), oscSyntaxDagger 1)}
  rw [dualOscSyntax_preserves_one_contract, hd]
  have hr (z : ℂ) (w : ChargeWord) :
      reflectChargeWord (ChargeWord.scale z w) = ChargeWord.scale z (reflectChargeWord w) := rfl
  rw [hr, canonicalKleinD_reflection_contract]
  congr 2
  apply congrArg₂ (fun t f => ({target := t, amplitude := f} : ChargeWord))
  · rfl
  · funext N
    simp [ChargeWord.scale, ChargeWord.adjoint, canonicalKleinSAdj,
      star_mul, mul_comm, mul_left_comm, canonicalKleinS, chargeShiftSEquiv]

theorem dressed_normal_multiplier_exchange {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) :
    dressedNormalMultiplier (M := M) (reflectHyperbolic P) false =
      dressedNormalMultiplier (M := M) P true ∧
    dressedNormalMultiplier (M := M) (reflectHyperbolic P) true =
      dressedNormalMultiplier (M := M) P false := by
  rcases gain_exchange P with ⟨hD, hS⟩
  constructor <;> funext n <;> simp [dressedNormalMultiplier, hD, hS]

theorem bare_normal_multiplier_self_adjoint {M : ℕ} (n : ℕ) :
    star (bareNormalMultiplier M n) = bareNormalMultiplier M n := by
  unfold bareNormalMultiplier
  split_ifs <;> simp [Complex.conj_ofReal]

theorem dressed_normal_vertex_D_contract {M h : ℕ} (hh : 0 < h)
    (P : Bosonize.Ch18.HyperbolicPair) (x : Position (2 * h)) :
    dualSeries (vertexWeylDressedNormal (M := M) hh P x false) =
      (fun n => ((vertexSeriesAdjoint (vertexWeylDressedNormal (M := M) hh (reflectHyperbolic P) x true)) n).map
        (vertexCoeffScale ((Bosonize.A01.canonicalRoot (2*h)) ^ (x.val : ℤ)))) := by
  sorry

theorem bare_normal_vertex_D_contract {M h : ℕ} (hh : 0 < h)
    (P : Bosonize.Ch18.HyperbolicPair) (x : Position (2 * h)) :
    dualSeries (vertexWeylBareNormal (M := M) hh P x false) =
      (fun n => ((vertexSeriesAdjoint (vertexWeylBareNormal (M := M) hh (reflectHyperbolic P) x true)) n).map
        (vertexCoeffScale ((Bosonize.A01.canonicalRoot (2*h)) ^ (x.val : ℤ)))) := by
  sorry

theorem duality_state_family_contract {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (N : Charge) (a : vertexCoeff M) :
    jointCoeffFunctional (reflectHyperbolic P) (reflectCharge N) (dualCoeff a) =
      jointCoeffFunctional P N a := by
  exact joint_functional_transport_from_action P N a

theorem duality_state_family_series_contract {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (N : Charge) (A : VertexSeries M) :
    jointSeriesFunctional (reflectHyperbolic P) (reflectCharge N) (dualSeries A) =
      jointSeriesFunctional P N A := by
  funext n
  simp only [jointSeriesFunctional, dualSeries, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  exact joint_functional_transport_from_action P N a

theorem duality_ordered_product_transport {M : ℕ}
    (P : Bosonize.Ch18.HyperbolicPair) (N : Charge)
    (A B : VertexSeries M) :
    jointSeriesFunctional (reflectHyperbolic P) (reflectCharge N)
        (vertexSeriesMul (dualSeries A) (dualSeries B)) =
      jointSeriesFunctional P N (vertexSeriesMul A B) := by
  rw [← dualSeries_product_contract]
  exact duality_state_family_series_contract P N (vertexSeriesMul A B)

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
