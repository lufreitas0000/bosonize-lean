import Bosonize.Core.V1S1OrderedWick

/-!
# V1-S2 Phase A: charge words and coefficientwise formal vertices

All oscillator products in this module are interpreted through A08's
polynomial representation.  The free algebra remains the syntax carrier;
the Phase A theorem contracts below record the representation and moment
obligations rather than asserting CCR equalities in that free algebra.
-/

namespace Bosonize.V1S2

open scoped BigOperators

abbrev Charge := ℤ × ℤ
abbrev ChargeVec := Charge →₀ ℂ
abbrev Position (L : ℕ) := ZMod L
def FormalSeries (A : Type*) := ℕ → A
abbrev JointCarrier (M : ℕ) :=
  TensorProduct ℂ ChargeVec (Bosonize.A08.OscPoly M)

abbrev JointBasisIndex (M : ℕ) := Charge × (Bosonize.A08.OscMode M →₀ ℕ)

noncomputable def jointBasisOf (M : ℕ) :
    Module.Basis (JointBasisIndex M) ℂ (JointCarrier M) :=
  Module.Basis.tensorProduct Finsupp.basisSingleOne
    (MvPolynomial.basisMonomials (Bosonize.A08.OscMode M) ℂ)

def jointBasisWeight {M : ℕ} (i : JointBasisIndex M) : ℂ :=
  (Bosonize.A08.oscMonomialNorm i.2 : ℂ)

/-- The product sesquilinear pairing on the actual algebraic tensor carrier,
defined by its tensor-product basis. The oscillator weight is A08's existing
monomial norm. This does not install a star operation on endomorphisms. -/
noncomputable def jointPairing {M : ℕ} (v u : JointCarrier M) : ℂ := by
  classical
  let b := jointBasisOf M
  exact ∑ i ∈ (b.repr v).support ∪ (b.repr u).support,
    star ((b.repr v) i) * jointBasisWeight i * (b.repr u) i

theorem jointPairing_basis_contract {M : ℕ} (i j : JointBasisIndex M) :
    jointPairing (jointBasisOf M i) (jointBasisOf M j) =
      if i = j then jointBasisWeight i else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp [jointPairing, jointBasisWeight]
  · simp [jointPairing, jointBasisWeight, hij, Ne.symm hij]

noncomputable def jointBasis (M : ℕ) (N : Charge) : JointCarrier M :=
  TensorProduct.tmul ℂ (Finsupp.single N 1) (1 : Bosonize.A08.OscPoly M)

def chargeCoordinate (N : Charge) : ChargeVec →ₗ[ℂ] ℂ where
  toFun := fun v => v N
  map_add' := by intro v w; rfl
  map_smul' := by intro z v; rfl

noncomputable def jointTensorFunctional {M : ℕ}
    (_hp : Bosonize.Ch18.HyperbolicPair) (N : Charge) : JointCarrier M →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    { toFun := fun v =>
        { toFun := fun p => v N * MvPolynomial.lcoeff ℂ 0 p
          map_add' := by intro p q; simp [mul_add]
          map_smul' := by intro z p; simp only [map_smul, RingHom.id_apply, smul_eq_mul]; ring }
      map_add' := by intro v w; ext p; simp [add_mul]
      map_smul' := by intro z v; ext p; simp [mul_assoc] }

@[simp] theorem jointTensorFunctional_tmul {M : ℕ}
    (hp : Bosonize.Ch18.HyperbolicPair) (N : Charge) (v : ChargeVec)
    (p : Bosonize.A08.OscPoly M) :
    jointTensorFunctional (M := M) hp N (TensorProduct.tmul ℂ v p) =
      v N * MvPolynomial.lcoeff ℂ 0 p := by
  simp [jointTensorFunctional]

def chargeGaugeExponent (h : ℕ) (N : Charge) : ℤ :=
  (h : ℤ) * N.1 + N.1 * (N.1 - 1) / 2 + N.2 * (N.2 - 1) / 2

noncomputable def chargeGauge (h : ℕ) (N : Charge) : ℂ :=
  (-1 : ℂ) ^ chargeGaugeExponent h N

def chargeShiftR (N : Charge) : Charge := (N.1 - 1, N.2)
def chargeShiftL (N : Charge) : Charge := (N.1, N.2 - 1)
def chargeShiftD (N : Charge) : Charge := (N.1 + 1, N.2 - 1)
def chargeShiftS (N : Charge) : Charge := (N.1 - 1, N.2 - 1)
def inverseShiftD (N : Charge) : Charge := (N.1 - 1, N.2 + 1)
def inverseShiftS (N : Charge) : Charge := (N.1 + 1, N.2 + 1)

def chargeShiftDEquiv : Charge ≃ Charge where
  toFun := chargeShiftD
  invFun := inverseShiftD
  left_inv := by intro N; rcases N with ⟨r,l⟩; simp [chargeShiftD, inverseShiftD]
  right_inv := by intro N; rcases N with ⟨r,l⟩; simp [chargeShiftD, inverseShiftD]

def chargeShiftSEquiv : Charge ≃ Charge where
  toFun := chargeShiftS
  invFun := inverseShiftS
  left_inv := by intro N; rcases N with ⟨r,l⟩; simp [chargeShiftS, inverseShiftS]
  right_inv := by intro N; rcases N with ⟨r,l⟩; simp [chargeShiftS, inverseShiftS]

def aD (N : Charge) : ℤ := N.2 - N.1 - 1
def aS (N : Charge) : ℤ := N.1 + N.2

noncomputable def chargePhase (L : ℕ) (a : ℤ) (x : Position L) : ℂ :=
  Bosonize.A01.integerCharacter (Bosonize.A01.canonicalRoot L) a (x.val : ℤ)

theorem chargePhaseLift_independent (L : ℕ) [NeZero L] (a x k : ℤ) :
    Bosonize.A01.integerCharacter (Bosonize.A01.canonicalRoot L) a
        (x + k * (L : ℤ)) =
      Bosonize.A01.integerCharacter (Bosonize.A01.canonicalRoot L) a x := by
  simpa [Bosonize.A01.integerCharacter] using
    (Bosonize.A01.character_representative_independent L
      (Bosonize.A01.canonicalRoot L) (Bosonize.A01.canonical_root_primitive L)
      a x 0 k)

/-- A monomial charge action is recorded by its target and source coefficient.
Composition below uses rightmost-first action on basis charges. -/
structure ChargeWord where
  target : Charge ≃ Charge
  amplitude : Charge → ℂ

/-- Charge monomials act on finite vectors by a finite sum over the source
support; no completion or infinite charge sum is introduced. -/
noncomputable def chargeWordAction (w : ChargeWord) (v : ChargeVec) : ChargeVec := by
  classical
  exact v.sum fun N z => z • (w.amplitude N • Finsupp.single (w.target N) 1)

theorem chargeWordAction_add_contract (w : ChargeWord) (v u : ChargeVec) :
    chargeWordAction w (v + u) = chargeWordAction w v + chargeWordAction w u := by
  classical
  unfold chargeWordAction
  apply Finsupp.sum_add_index
  · intro N hN; simp
  · intro N hN z₁ z₂; simp [add_smul]

theorem chargeWordAction_smul_contract (w : ChargeWord) (z : ℂ) (v : ChargeVec) :
    chargeWordAction w (z • v) = z • chargeWordAction w v := by
  classical
  let h : Charge → ℂ → ChargeVec := fun N b =>
    b • (w.amplitude N • Finsupp.single (w.target N) (1 : ℂ))
  change (z • v).sum h = z • v.sum h
  calc
    (z • v).sum h = v.sum (fun N b => h N (z * b)) :=
      Finsupp.sum_smul_index (by intro N; simp [h])
    _ = v.sum (fun N b => z • h N b) := by
      apply Finsupp.sum_congr
      intro N hN
      simp [h, mul_assoc]
    _ = z • v.sum h :=
      (Finsupp.smul_sum).symm

noncomputable def chargeWordActionLinear (w : ChargeWord) : ChargeVec →ₗ[ℂ] ChargeVec where
  toFun := chargeWordAction w
  map_add' := chargeWordAction_add_contract w
  map_smul' := chargeWordAction_smul_contract w

theorem chargeWordAction_basis_contract (w : ChargeWord) (N : Charge) :
    chargeWordAction w (Finsupp.single N 1) =
      w.amplitude N • Finsupp.single (w.target N) 1 := by
  classical
  simp [chargeWordAction]

noncomputable def chargePairing (v u : ChargeVec) : ℂ :=
  ∑ N ∈ v.support ∪ u.support, star (v N) * u N

theorem jointPairing_tmul_factor_contract {M : ℕ}
    (v u : ChargeVec) (p q : Bosonize.A08.OscPoly M) :
    jointPairing (TensorProduct.tmul ℂ v p) (TensorProduct.tmul ℂ u q) =
      chargePairing v u * Bosonize.A08.oscPairing M p q := by sorry

def ChargeWord.comp (f g : ChargeWord) : ChargeWord where
  target := g.target.trans f.target
  amplitude := fun N => g.amplitude N * f.amplitude (g.target N)

def ChargeWord.adjoint (f : ChargeWord) : ChargeWord where
  target := f.target.symm
  amplitude := fun N => star (f.amplitude (f.target.symm N))

theorem chargeWord_comp_action_contract (f g : ChargeWord) (v : ChargeVec) :
    chargeWordAction (ChargeWord.comp f g) v =
      chargeWordAction f (chargeWordAction g v) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp [chargeWordAction]
  | add v u hv hu =>
      rw [chargeWordAction_add_contract (ChargeWord.comp f g) v u, hv, hu,
        chargeWordAction_add_contract g v u,
        chargeWordAction_add_contract f (chargeWordAction g v) (chargeWordAction g u)]
  | single a z => simp [chargeWordAction, ChargeWord.comp, mul_assoc]

theorem chargeWord_adjoint_pairing_contract (f : ChargeWord) (v u : ChargeVec) :
    chargePairing (chargeWordAction f v) u =
      chargePairing v (chargeWordAction (ChargeWord.adjoint f) u) := by sorry

noncomputable def kleinD (L : ℕ) (x : Position L) : ChargeWord where
  target := chargeShiftDEquiv
  amplitude := fun N => (-1 : ℂ) ^ N.1 * chargePhase L (aD N) x

noncomputable def kleinS (L : ℕ) (x : Position L) : ChargeWord where
  target := chargeShiftSEquiv
  amplitude := fun N => (-1 : ℂ) ^ N.1 * chargePhase L (aS N) x

def ChargeWord.scale (z : ℂ) (w : ChargeWord) : ChargeWord where
  target := w.target
  amplitude := fun N => z * w.amplitude N

/-- The research shifts above are transported to the canonical CH13 basis by
the diagonal gauge. The oscillator tensor factor is unaffected. -/
noncomputable def canonicalKleinD (h : ℕ) (L : ℕ) (x : Position L) : ChargeWord where
  target := chargeShiftDEquiv
  amplitude := fun N => chargeGauge h (chargeShiftD N) *
    (kleinD L x).amplitude N * star (chargeGauge h N)

noncomputable def canonicalKleinS (h : ℕ) (L : ℕ) (x : Position L) : ChargeWord where
  target := chargeShiftSEquiv
  amplitude := fun N => chargeGauge h (chargeShiftS N) *
    (kleinS L x).amplitude N * star (chargeGauge h N)

noncomputable def kleinDAdj (L : ℕ) (x : Position L) : ChargeWord where
  target := chargeShiftDEquiv.symm
  amplitude := fun N => star ((kleinD L x).amplitude (inverseShiftD N))

noncomputable def kleinSAdj (L : ℕ) (x : Position L) : ChargeWord where
  target := chargeShiftSEquiv.symm
  amplitude := fun N => star ((kleinS L x).amplitude (inverseShiftS N))

noncomputable def canonicalKleinDAdj (h : ℕ) (L : ℕ) (x : Position L) : ChargeWord where
  target := chargeShiftDEquiv.symm
  amplitude := fun N => star ((canonicalKleinD h L x).amplitude (inverseShiftD N))

noncomputable def canonicalKleinSAdj (h : ℕ) (L : ℕ) (x : Position L) : ChargeWord where
  target := chargeShiftSEquiv.symm
  amplitude := fun N => star ((canonicalKleinS h L x).amplitude (inverseShiftS N))

def chargeBasisExpectation (N : Charge) (w : ChargeWord) : ℂ :=
  if w.target N = N then w.amplitude N else 0

def chargeSelection (N : Charge) (w : ChargeWord) : Prop := w.target N = N

/- The oscillator coefficient algebra is a monoid algebra on finite words.
Its explicit dagger is conjugation plus word reversal and creator/annihilator
swap; evaluation sends it to A08's existing free-algebra representation. -/
instance oscillatorWordMonoid (M : ℕ) : Monoid (List (Bosonize.A08.OscGen M)) where
  one := []
  mul := List.append
  mul_assoc := List.append_assoc
  one_mul := List.nil_append
  mul_one := List.append_nil

abbrev OscSyntax (M : ℕ) :=
  MonoidAlgebra ℂ (List (Bosonize.A08.OscGen M))

noncomputable def oscFreeToSyntax (M : ℕ) :
    Bosonize.A08.OscAlgebra M →ₐ[ℂ] OscSyntax M :=
  FreeAlgebra.lift ℂ (fun g => (MonoidAlgebra.single [g] (1 : ℂ) : OscSyntax M))

noncomputable def oscSyntaxDagger {M : ℕ} (a : OscSyntax M) : OscSyntax M := by
  classical
  exact MonoidAlgebra.ofCoeff
    (Finsupp.sum a.coeff fun w z =>
      Finsupp.single (Bosonize.A08.wordDagger w) (star z))

noncomputable def oscSyntaxEval {M : ℕ} (a : OscSyntax M) : Bosonize.A08.OscAlgebra M := by
  classical
  exact Finsupp.sum a.coeff fun w z => z • Bosonize.A08.wordElement M w

theorem oscSyntax_roundtrip_freeAlgebra_contract {M : ℕ}
    (a : Bosonize.A08.OscAlgebra M) :
    oscSyntaxEval (oscFreeToSyntax M a) = a := by sorry

theorem oscSyntaxEval_one_contract {M : ℕ} :
    oscSyntaxEval (1 : OscSyntax M) = 1 := by
  classical
  change oscSyntaxEval (MonoidAlgebra.single ([] : List (Bosonize.A08.OscGen M)) 1) = 1
  simp [oscSyntaxEval, Bosonize.A08.wordElement]

theorem oscSyntaxEval_mul_contract {M : ℕ} (a b : OscSyntax M) :
    oscSyntaxEval (a * b) = oscSyntaxEval a * oscSyntaxEval b := by
  let wordMap : List (Bosonize.A08.OscGen M) →* Bosonize.A08.OscAlgebra M :=
    { toFun := Bosonize.A08.wordElement M
      map_one' := by
        change Bosonize.A08.wordElement M ([] : List (Bosonize.A08.OscGen M)) = 1
        simp [Bosonize.A08.wordElement]
      map_mul' := by
        intro x y
        change Bosonize.A08.wordElement M (x ++ y) =
          Bosonize.A08.wordElement M x * Bosonize.A08.wordElement M y
        simp [Bosonize.A08.wordElement, List.map_append, List.prod_append] }
  have heval (x : OscSyntax M) :
      oscSyntaxEval x = (MonoidAlgebra.lift ℂ (Bosonize.A08.OscAlgebra M)
        (List (Bosonize.A08.OscGen M)) wordMap) x := by
    simp [oscSyntaxEval, MonoidAlgebra.lift_apply, wordMap]
  rw [heval (a * b), heval a, heval b]
  exact (MonoidAlgebra.lift ℂ (Bosonize.A08.OscAlgebra M)
    (List (Bosonize.A08.OscGen M)) wordMap).map_mul a b

theorem oscSyntaxDagger_involutive_contract {M : ℕ} (a : OscSyntax M) :
    oscSyntaxDagger (oscSyntaxDagger a) = a := by sorry

theorem oscSyntaxDagger_mul_contract {M : ℕ} (a b : OscSyntax M) :
    oscSyntaxDagger (a * b) = oscSyntaxDagger b * oscSyntaxDagger a := by sorry

def vertexCoeff (M : ℕ) := ChargeWord × OscSyntax M

noncomputable def vertexCoeffMul {M : ℕ} (a b : vertexCoeff M) : vertexCoeff M :=
  (ChargeWord.comp a.1 b.1, a.2 * b.2)

noncomputable def vertexCoeffAdjoint {M : ℕ} (a : vertexCoeff M) : vertexCoeff M :=
  (ChargeWord.adjoint a.1, oscSyntaxDagger a.2)

def FormalSeries.add {A : Type*} [Add A] (f g : FormalSeries A) : FormalSeries A :=
  fun n => f n + g n

/- A coefficient is a finite multiset of monomials. Multiplicity records
   addition, while forgetting presentation order makes the formal algebra's
   Cauchy product and coefficientwise adjoint strict operations. -/
abbrev VertexSeries (M : ℕ) := FormalSeries (Multiset (vertexCoeff M))

noncomputable def vertexSeriesMul {M : ℕ} (f g : VertexSeries M) : VertexSeries M := fun n =>
  ∑ k ∈ Finset.range (n + 1),
    (f k).bind fun a => (g (n - k)).map fun b => vertexCoeffMul a b

noncomputable def vertexSeriesAdjoint {M : ℕ} (f : VertexSeries M) : VertexSeries M :=
  fun n => (f n).map vertexCoeffAdjoint

noncomputable def dressedModeForm {M : ℕ} (c s : ℝ)
    (creator : Bool) (ν : Bosonize.A06.Orientation) (m : Fin M) :
    Bosonize.V1S1.OscLinearForm M :=
  Bosonize.V1S1.dressedGeneratorForm c s (creator, (ν, m))

def epsilon (ν : Bosonize.A06.Orientation) : ℤ :=
  if ν = Bosonize.A06.Orientation.right then 1 else -1

noncomputable def qForm {M L : ℕ} (c s : ℝ) (ν : Bosonize.A06.Orientation)
    (x : Position L) : Bosonize.V1S1.OscLinearForm M := by
  classical
  exact ∑ m : Fin M,
    ((((Bosonize.A01.canonicalRoot L) ^ (-(epsilon ν) * ((m.val : ℤ) + 1) * (x.val : ℤ))) /
        ((m.val : ℂ) + 1)) • dressedModeForm c s true ν m +
      (((Bosonize.A01.canonicalRoot L) ^ (epsilon ν * ((m.val : ℤ) + 1) * (x.val : ℤ))) /
        ((m.val : ℂ) + 1)) • dressedModeForm c s false ν m)

noncomputable def xDForm {M L : ℕ} (hp : Bosonize.Ch18.HyperbolicPair)
    (x : Position L) : Bosonize.V1S1.OscLinearForm M :=
  ((hp.c - hp.s : ℝ) : ℂ) •
    (qForm hp.c hp.s Bosonize.A06.Orientation.right x +
      qForm hp.c hp.s Bosonize.A06.Orientation.left x)

noncomputable def xSForm {M L : ℕ} (hp : Bosonize.Ch18.HyperbolicPair)
    (x : Position L) : Bosonize.V1S1.OscLinearForm M :=
  ((hp.c + hp.s : ℝ) : ℂ) •
    (qForm hp.c hp.s Bosonize.A06.Orientation.right x -
      qForm hp.c hp.s Bosonize.A06.Orientation.left x)

def gainD (hp : Bosonize.Ch18.HyperbolicPair) : ℝ := (hp.c - hp.s) ^ 2
def gainS (hp : Bosonize.Ch18.HyperbolicPair) : ℝ := (hp.c + hp.s) ^ 2

noncomputable def scalarExp (a : ℂ) : FormalSeries ℂ := fun n => a ^ n / (n.factorial : ℂ)

noncomputable def oscillatorExpWithScalar {M L : ℕ} (hp : Bosonize.Ch18.HyperbolicPair)
    (x : Position L) (channel : Bool) (ι : ℂ) : FormalSeries (OscSyntax M) :=
  fun n => ((n.factorial : ℂ)⁻¹) •
    ((ι • oscFreeToSyntax M (Bosonize.V1S1.linearElement
      (if channel then xSForm hp x else xDForm hp x))) ^ n)

noncomputable def oscillatorExp {M L : ℕ} (hp : Bosonize.Ch18.HyperbolicPair)
    (x : Position L) (channel : Bool) : FormalSeries (OscSyntax M) :=
  oscillatorExpWithScalar hp x channel Complex.I

noncomputable def harmonicCutoff (M : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 M, (m : ℝ)⁻¹

noncomputable def dirichletCutoff (L M : ℕ) (x y : Position L) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M,
    (1 - Real.cos (2 * Real.pi * (m : ℝ) * ((x.val : ℤ) - (y.val : ℤ)) / (L : ℝ))) /
      (m : ℝ)

noncomputable def vertexWeyl {M h : ℕ} (_hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (x : Position (2 * h))
    (channel : Bool) : VertexSeries M := by
  classical
  exact fun n =>
    { (ChargeWord.scale ((2 * h : ℕ) : ℂ)⁻¹
      (if channel then canonicalKleinS h (2 * h) x else canonicalKleinD h (2 * h) x),
      oscillatorExp hp x channel n) }

noncomputable def vertexWeylAdj {M h : ℕ} (_hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (x : Position (2 * h))
    (channel : Bool) : VertexSeries M :=
  vertexSeriesAdjoint (vertexWeyl (M := M) _hh hp x channel)

noncomputable def jointCoeffAction {M : ℕ} (hp : Bosonize.Ch18.HyperbolicPair)
    (a : vertexCoeff M) : JointCarrier M →ₗ[ℂ] JointCarrier M :=
  TensorProduct.map (chargeWordActionLinear a.1)
    (Bosonize.A08.oscRep M
      (Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (oscSyntaxEval a.2)))

noncomputable def jointCoeffFunctional {M : ℕ} (hp : Bosonize.Ch18.HyperbolicPair)
    (N : Charge) (a : vertexCoeff M) : ℂ :=
  jointTensorFunctional (M := M) hp N
    (jointCoeffAction hp a (jointBasis M N))

theorem jointCoeffAction_mul_contract {M : ℕ}
    (hp : Bosonize.Ch18.HyperbolicPair) (a b : vertexCoeff M) :
    jointCoeffAction hp (vertexCoeffMul a b) =
      (jointCoeffAction hp a).comp (jointCoeffAction hp b) := by sorry

theorem jointCoeffAction_adjoint_factor_contract {M : ℕ}
    (hp : Bosonize.Ch18.HyperbolicPair) (a : vertexCoeff M) :
    jointCoeffAction hp (vertexCoeffAdjoint a) =
      TensorProduct.map (chargeWordActionLinear (ChargeWord.adjoint a.1))
        (Bosonize.A08.oscRep M
          (Bosonize.A08.bogoliubovMap M hp.c (-hp.s)
            (oscSyntaxEval (oscSyntaxDagger a.2)))) := by rfl

/-- The coefficient dagger is the adjoint of the represented operator for
the explicit product pairing on the joint carrier. This is the proof-relevant
bridge used for the vertex-series adjoint; no star on arbitrary endomorphisms
is assumed. -/
theorem jointCoeffAction_adjoint_pairing_contract {M : ℕ}
    (hp : Bosonize.Ch18.HyperbolicPair) (a : vertexCoeff M)
    (v u : JointCarrier M) :
    jointPairing (jointCoeffAction hp a v) u =
      jointPairing v (jointCoeffAction hp (vertexCoeffAdjoint a) u) := by sorry

theorem jointCoeffFunctional_is_matrix_coefficient_contract {M : ℕ}
    (hp : Bosonize.Ch18.HyperbolicPair) (N : Charge) (a : vertexCoeff M) :
    jointCoeffFunctional hp N a =
      jointPairing (jointBasis M N) (jointCoeffAction hp a (jointBasis M N)) := by sorry

theorem jointCoeffFunctional_product_contract {M : ℕ}
    (hp : Bosonize.Ch18.HyperbolicPair) (N : Charge) (a : vertexCoeff M) :
    jointCoeffFunctional hp N a =
      chargeBasisExpectation N a.1 * Bosonize.A08.omegaP M hp (oscSyntaxEval a.2) := by
  simp only [jointCoeffFunctional, jointCoeffAction, jointBasis,
    TensorProduct.map_tmul, jointTensorFunctional_tmul]
  change chargeWordAction a.1 (Finsupp.single N 1) N *
      MvPolynomial.lcoeff ℂ 0
        (Bosonize.A08.oscRep M
          (Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (oscSyntaxEval a.2)) 1) = _
  rw [chargeWordAction_basis_contract]
  simp [chargeBasisExpectation, Bosonize.A08.omegaP, Bosonize.A08.omega0,
    Finsupp.single_apply]

theorem jointCoeffFunctional_adjoint_contract {M : ℕ}
    (hp : Bosonize.Ch18.HyperbolicPair) (N : Charge) (a : vertexCoeff M) :
    jointCoeffFunctional hp N (vertexCoeffAdjoint a) =
      star (jointCoeffFunctional hp N a) := by sorry

noncomputable def jointSeriesCoeffFunctional {M : ℕ} (hp : Bosonize.Ch18.HyperbolicPair)
    (N : Charge) (a : vertexCoeff M) : ℂ := jointCoeffFunctional hp N a

noncomputable def jointSeriesFunctional {M : ℕ} (hp : Bosonize.Ch18.HyperbolicPair)
    (N : Charge) (f : VertexSeries M) : FormalSeries ℂ := fun n =>
  ((f n).map (jointCoeffFunctional hp N)).sum

noncomputable def expectedWeylCorrelator {M h : ℕ} (_hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (N : Charge) (x y : Position (2 * h))
    (channel : Bool) : FormalSeries ℂ := fun n =>
  let k := n / 2
  let g : ℂ := if channel then (gainS hp : ℂ) else (gainD hp : ℂ)
  let d : ℂ := dirichletCutoff (2 * h) M x y
  let a := if channel then aS N else aD N
  let phase := Bosonize.A01.integerCharacter (Bosonize.A01.canonicalRoot (2 * h)) a
    ((y.val : ℤ) - (x.val : ℤ))
  if n % 2 = 0 then
    ((2 * h : ℕ) : ℂ)⁻¹ ^ 2 * phase * ((-2 * g * (d : ℂ)) ^ k / (k.factorial : ℂ))
  else 0

def scalarSeriesMul (f g : FormalSeries ℂ) : FormalSeries ℂ := fun n =>
  ∑ k ∈ Finset.range (n + 1), f k * g (n - k)

def vertexSeriesScalarMul {M : ℕ} (s : FormalSeries ℂ) (v : VertexSeries M) :
    VertexSeries M := fun n =>
  ∑ k ∈ Finset.range (n + 1),
    (v (n - k)).map fun a => (ChargeWord.scale (s k) a.1, a.2)


noncomputable def dressedNormalMultiplier {M : ℕ} (hp : Bosonize.Ch18.HyperbolicPair)
    (channel : Bool) : FormalSeries ℂ := fun n =>
  let k := n / 2
  if n % 2 = 0 then
    ((if channel then gainS hp else gainD hp) * harmonicCutoff M : ℝ) ^ k /
      (k.factorial : ℝ) |> fun r => (r : ℂ)
  else 0

noncomputable def bareNormalMultiplier (M : ℕ) : FormalSeries ℂ := fun n =>
  let k := n / 2
  if n % 2 = 0 then
    (harmonicCutoff M ^ k / (k.factorial : ℝ) : ℝ) |> fun r => (r : ℂ)
  else 0

noncomputable def vertexWeylDressedNormal {M h : ℕ} (hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (x : Position (2 * h))
    (channel : Bool) : VertexSeries M :=
  vertexSeriesScalarMul (dressedNormalMultiplier (M := M) hp channel)
    (vertexWeyl (M := M) hh hp x channel)

noncomputable def vertexWeylBareNormal {M h : ℕ} (hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (x : Position (2 * h))
    (channel : Bool) : VertexSeries M :=
  vertexSeriesScalarMul (bareNormalMultiplier M) (vertexWeyl (M := M) hh hp x channel)


noncomputable def dressedNormalCorrelator {M h : ℕ} (hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (N : Charge) (x y : Position (2 * h))
    (channel : Bool) : FormalSeries ℂ :=
  scalarSeriesMul (expectedWeylCorrelator (M := M) hh hp N x y channel)
    (scalarSeriesMul (dressedNormalMultiplier (M := M) hp channel)
      (dressedNormalMultiplier (M := M) hp channel))

noncomputable def bareNormalCorrelator {M h : ℕ} (hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (N : Charge) (x y : Position (2 * h))
    (channel : Bool) : FormalSeries ℂ :=
  scalarSeriesMul (expectedWeylCorrelator (M := M) hh hp N x y channel)
    (scalarSeriesMul (bareNormalMultiplier M) (bareNormalMultiplier M))

theorem coefficientwise_weyl_correlator_contract {M h : ℕ} (hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (N : Charge) (x y : Position (2 * h))
    (channel : Bool) :
    jointSeriesFunctional (M := M) hp N
      (vertexSeriesMul (M := M) (vertexWeylAdj (M := M) hh hp x channel)
        (vertexWeyl (M := M) hh hp y channel)) =
        expectedWeylCorrelator (M := M) hh hp N x y channel := by sorry

theorem dressed_normal_prefactor_contract {M h : ℕ} (hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (N : Charge) (x y : Position (2 * h))
    (channel : Bool) :
    jointSeriesFunctional (M := M) hp N
      (vertexSeriesMul (M := M)
        (vertexSeriesScalarMul (dressedNormalMultiplier (M := M) hp channel)
          (vertexWeylAdj (M := M) hh hp x channel))
        (vertexWeylDressedNormal hh hp y channel)) =
      dressedNormalCorrelator (M := M) hh hp N x y channel := by sorry

theorem bare_normal_prefactor_contract {M h : ℕ} (hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (N : Charge) (x y : Position (2 * h))
    (channel : Bool) :
    jointSeriesFunctional (M := M) hp N
      (vertexSeriesMul (M := M)
        (vertexSeriesScalarMul (bareNormalMultiplier M) (vertexWeylAdj (M := M) hh hp x channel))
        (vertexWeylBareNormal hh hp y channel)) =
      bareNormalCorrelator (M := M) hh hp N x y channel := by sorry

/-! The following contracts are intentionally Phase A placeholders. -/

theorem chargeGauge_unitary_contract (h : ℕ) (N : Charge) :
    ‖chargeGauge h N‖ = 1 := by
  simp [chargeGauge]

theorem gauge_adapter_right_contract (h : ℕ) (N : Charge) :
    chargeGauge h (chargeShiftR N) / chargeGauge h N =
      (-1 : ℂ) ^ (h + N.1 - 1) := by sorry

theorem gauge_adapter_left_contract (h : ℕ) (N : Charge) :
    chargeGauge h (chargeShiftL N) / chargeGauge h N =
      (-1 : ℂ) ^ (N.2 - 1) := by sorry

theorem gauge_adapter_left_klein_contract (h : ℕ) (N : Charge) :
    (-1 : ℂ) ^ N.1 *
        (chargeGauge h (chargeShiftL N) / chargeGauge h N) =
      (-1 : ℂ) ^ (N.1 + N.2 - 1) := by sorry

theorem source_phase_product_contract (L : ℕ) (_hL : 0 < L) (a : ℤ)
    (x y : Position L) :
    chargePhase L a x * star (chargePhase L a y) =
      Bosonize.A01.integerCharacter (Bosonize.A01.canonicalRoot L) a
        ((x.val : ℤ) - (y.val : ℤ)) := by
  have hprim : IsPrimitiveRoot (Bosonize.A01.canonicalRoot L) L :=
    @Bosonize.A01.canonical_root_primitive L ⟨Nat.ne_of_gt _hL⟩
  unfold chargePhase
  rw [@Bosonize.A01.complex_character_conj L ⟨Nat.ne_of_gt _hL⟩
    (Bosonize.A01.canonicalRoot L) hprim a (y.val : ℤ)]
  simp only [Bosonize.A01.integerCharacter]
  rw [← zpow_add₀ (hprim.ne_zero (Nat.ne_of_gt _hL))
    (a * (x.val : ℤ)) (-a * (y.val : ℤ))]
  congr 1
  ring

theorem charge_selection_D_contract (L : ℕ) (_hL : 0 < L) (x y : Position L) (N : Charge) :
    chargeBasisExpectation N
      (ChargeWord.comp (kleinDAdj L x) (kleinD L y)) =
        Bosonize.A01.integerCharacter (Bosonize.A01.canonicalRoot L)
          (aD N) ((y.val : ℤ) - (x.val : ℤ)) := by sorry

theorem charge_selection_S_contract (L : ℕ) (_hL : 0 < L) (x y : Position L) (N : Charge) :
    chargeBasisExpectation N
      (ChargeWord.comp (kleinSAdj L x) (kleinS L y)) =
        Bosonize.A01.integerCharacter (Bosonize.A01.canonicalRoot L)
          (aS N) ((y.val : ℤ) - (x.val : ℤ)) := by sorry

theorem canonical_charge_selection_D_contract (h : ℕ) (L : ℕ) (_hL : 0 < L)
    (x y : Position L) (N : Charge) :
    chargeBasisExpectation N
      (ChargeWord.comp (canonicalKleinDAdj h L x) (canonicalKleinD h L y)) =
        Bosonize.A01.integerCharacter (Bosonize.A01.canonicalRoot L)
          (aD N) ((y.val : ℤ) - (x.val : ℤ)) := by sorry

theorem canonical_charge_selection_S_contract (h : ℕ) (L : ℕ) (_hL : 0 < L)
    (x y : Position L) (N : Charge) :
    chargeBasisExpectation N
      (ChargeWord.comp (canonicalKleinSAdj h L x) (canonicalKleinS h L y)) =
        Bosonize.A01.integerCharacter (Bosonize.A01.canonicalRoot L)
          (aS N) ((y.val : ℤ) - (x.val : ℤ)) := by sorry

theorem same_channel_commutator_contract {M h : ℕ} (_hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (x y : Position (2 * h)) (channel : Bool) :
    Bosonize.V1S1.contraction hp
      (if channel then xSForm (M := M) hp x else xDForm (M := M) hp x)
      (if channel then xSForm (M := M) hp y else xDForm (M := M) hp y) =
    Bosonize.V1S1.contraction hp
      (if channel then xSForm (M := M) hp y else xDForm (M := M) hp y)
      (if channel then xSForm (M := M) hp x else xDForm (M := M) hp x) := by sorry

/-- The commutation claim is on the A08 polynomial representation, not a
literal CCR equality in its free-algebra syntax. -/
theorem represented_same_channel_commutator_contract {M h : ℕ} (_hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (x y : Position (2 * h)) (channel : Bool) :
    Bosonize.A08.oscRep M
        (Bosonize.V1S1.linearElement
          (if channel then xSForm (M := M) hp x else xDForm (M := M) hp x)) *
      Bosonize.A08.oscRep M
        (Bosonize.V1S1.linearElement
          (if channel then xSForm (M := M) hp y else xDForm (M := M) hp y)) =
    Bosonize.A08.oscRep M
        (Bosonize.V1S1.linearElement
          (if channel then xSForm (M := M) hp y else xDForm (M := M) hp y)) *
      Bosonize.A08.oscRep M
        (Bosonize.V1S1.linearElement
          (if channel then xSForm (M := M) hp x else xDForm (M := M) hp x)) := by sorry

theorem field_adjoint_on_polynomials_contract {M L : ℕ}
    (hp : Bosonize.Ch18.HyperbolicPair) (x : Position L) (channel : Bool)
    (p q : Bosonize.A08.OscPoly M) :
    Bosonize.A08.oscPairing M p
      (Bosonize.A08.oscRep M (Bosonize.V1S1.linearElement
        (if channel then xSForm (M := M) hp x else xDForm (M := M) hp x)) q) =
    Bosonize.A08.oscPairing M
      (Bosonize.A08.oscRep M (Bosonize.V1S1.linearElement
        (if channel then xSForm (M := M) hp x else xDForm (M := M) hp x)) p) q := by sorry

theorem oscillatorExp_adjoint_coefficient_contract {M h : ℕ} (_hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (x : Position (2 * h)) (channel : Bool)
    (n : ℕ) (p q : Bosonize.A08.OscPoly M) :
    Bosonize.A08.oscPairing M p
      (Bosonize.A08.oscRep M
        (Bosonize.A08.bogoliubovMap M hp.c (-hp.s)
          (oscSyntaxEval (oscillatorExp hp x channel n))) q) =
    Bosonize.A08.oscPairing M
      (Bosonize.A08.oscRep M
        (Bosonize.A08.bogoliubovMap M hp.c (-hp.s)
          (oscSyntaxEval (oscillatorExpWithScalar hp x channel (-Complex.I) n))) p) q := by sorry

theorem oscillator_syntax_dagger_inverse_pullback_represents_adjoint_contract {M : ℕ}
    (hp : Bosonize.Ch18.HyperbolicPair)
    (a : OscSyntax M) (p q : Bosonize.A08.OscPoly M) :
    Bosonize.A08.oscPairing M p
      (Bosonize.A08.oscRep M
        (Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (oscSyntaxEval a)) q) =
    Bosonize.A08.oscPairing M
      (Bosonize.A08.oscRep M
        (Bosonize.A08.bogoliubovMap M hp.c (-hp.s)
          (oscSyntaxEval (oscSyntaxDagger a))) p) q := by sorry

theorem vertexSeriesAdjoint_reverses_product_contract {M : ℕ}
    (f g : VertexSeries M) :
    vertexSeriesAdjoint (vertexSeriesMul f g) =
      vertexSeriesMul (vertexSeriesAdjoint g) (vertexSeriesAdjoint f) := by sorry

theorem difference_variance_contract {M h : ℕ} (_hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (x y : Position (2 * h)) (channel : Bool) :
    Bosonize.V1S1.contraction hp
      (if channel then xSForm (M := M) hp y - xSForm (M := M) hp x
        else xDForm (M := M) hp y - xDForm (M := M) hp x)
      (if channel then xSForm (M := M) hp y - xSForm (M := M) hp x
        else xDForm (M := M) hp y - xDForm (M := M) hp x) =
      (4 : ℂ) * (if channel then gainS hp else gainD hp : ℂ) *
        (dirichletCutoff (2 * h) M x y : ℂ) := by sorry

end Bosonize.V1S2
