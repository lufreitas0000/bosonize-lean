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
      chargePairing v u * Bosonize.A08.oscPairing M p q := by
  classical
  let b := jointBasisOf M
  have hrepr (r : ChargeVec) (s : Bosonize.A08.OscPoly M) (i : JointBasisIndex M) :
      b.repr (TensorProduct.tmul ℂ r s) i = s.coeff i.2 * r i.1 := by
    rcases i with ⟨N, k⟩
    change (Module.Basis.tensorProduct Finsupp.basisSingleOne
      (MvPolynomial.basisMonomials (Bosonize.A08.OscMode M) ℂ)).repr
        (TensorProduct.tmul ℂ r s) (N, k) = _
    rw [Module.Basis.tensorProduct_repr_tmul_apply]
    rfl
  have hleft (r s : JointCarrier M) : jointPairing r s =
      ∑ i ∈ (b.repr r).support, star (b.repr r i) * jointBasisWeight i * b.repr s i := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro i _ hi
    simp [Finsupp.notMem_support_iff.mp hi]
  have hcharge : chargePairing v u = ∑ N ∈ v.support, star (v N) * u N := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro i _ hi
    simp [Finsupp.notMem_support_iff.mp hi]
  have hsupp : (b.repr (TensorProduct.tmul ℂ v p)).support ⊆ v.support ×ˢ p.support := by
    intro i hi
    have hn : p.coeff i.2 * v i.1 ≠ 0 := by
      simpa only [Finsupp.mem_support_iff, hrepr] using hi
    exact Finset.mem_product.mpr ⟨Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hn),
      MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hn)⟩
  rw [hleft]
  calc
    _ = ∑ i ∈ v.support ×ˢ p.support,
        star (b.repr (TensorProduct.tmul ℂ v p) i) * jointBasisWeight i *
          b.repr (TensorProduct.tmul ℂ u q) i := by
      apply Finset.sum_subset hsupp
      intro i _ hi
      simp [Finsupp.notMem_support_iff.mp hi]
    _ = (∑ N ∈ v.support, star (v N) * u N) *
        Bosonize.A08.oscPairing M p q := by
      simp only [Finset.sum_product, hrepr, jointBasisWeight, star_mul,
        Bosonize.A08.oscPairing, MvPolynomial.lcoeff_apply]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro N _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = chargePairing v u * Bosonize.A08.oscPairing M p q := by rw [hcharge]

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
      chargePairing v (chargeWordAction (ChargeWord.adjoint f) u) := by
  classical
  have hleft (x y : ChargeVec) : chargePairing x y =
      ∑ N ∈ x.support, star (x N) * y N := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro N _ hN
    simp [Finsupp.notMem_support_iff.mp hN]
  have hright (x y : ChargeVec) : chargePairing x y =
      ∑ N ∈ y.support, star (x N) * y N := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro N _ hN
    simp [Finsupp.notMem_support_iff.mp hN]
  have hsingle (N : Charge) (z : ℂ) (y : ChargeVec) :
      chargePairing (Finsupp.single N z) y = star z * y N := by
    rw [hleft]
    change (Finsupp.single N z).sum (fun N a => star a * y N) = _
    exact Finsupp.sum_single_index (by simp)
  have hadd (x y z : ChargeVec) :
      chargePairing (x + y) z = chargePairing x z + chargePairing y z := by
    simp only [hright, Finsupp.add_apply, star_add, add_mul, Finset.sum_add_distrib]
  induction v using Finsupp.induction_linear with
  | zero => simp [chargeWordAction, chargePairing]
  | add v w hv hw =>
      rw [chargeWordAction_add_contract, hadd, hadd, hv, hw]
  | single N z =>
      have haction (w : ChargeWord) (x : ChargeVec) (K : Charge) :
          chargeWordAction w x K = x (w.target.symm K) * w.amplitude (w.target.symm K) := by
        unfold chargeWordAction
        rw [Finsupp.sum_apply]
        simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, mul_ite,
          mul_one, mul_zero, ← Equiv.eq_symm_apply]
        simpa using
          (Finsupp.sum_eq_single (f := x) (w.target.symm K)
            (g := fun b c => if b = w.target.symm K then c * w.amplitude b else 0)
            (by intro b _ hne; simp [hne]) (by simp))
      have hsact : chargeWordAction f (Finsupp.single N z) =
          Finsupp.single (f.target N) (z * f.amplitude N) := by
        simp [chargeWordAction]
      rw [hsact, hsingle, hsingle, haction]
      simp [ChargeWord.adjoint, star_mul, mul_assoc, mul_comm]

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
    oscSyntaxEval (oscFreeToSyntax M a) = a := by
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
  let evalHom := MonoidAlgebra.lift ℂ (Bosonize.A08.OscAlgebra M)
    (List (Bosonize.A08.OscGen M)) wordMap
  have heval (x : OscSyntax M) : oscSyntaxEval x = evalHom x := by
    simp [oscSyntaxEval, evalHom, MonoidAlgebra.lift_apply, wordMap]
  have hcomp : evalHom.comp (oscFreeToSyntax M) = AlgHom.id ℂ (Bosonize.A08.OscAlgebra M) := by
    ext g
    simp [oscFreeToSyntax, evalHom, wordMap, Bosonize.A08.wordElement]
  rw [heval]
  exact AlgHom.congr_fun hcomp a

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
    oscSyntaxDagger (oscSyntaxDagger a) = a := by
  classical
  have hword (w : List (Bosonize.A08.OscGen M)) :
      Bosonize.A08.wordDagger (Bosonize.A08.wordDagger w) = w := by
    simp [Bosonize.A08.wordDagger, List.map_reverse, List.map_map, Function.comp_def]
  simp only [oscSyntaxDagger, MonoidAlgebra.coeff_ofCoeff]
  rw [Finsupp.sum_sum_index (by intro w; simp)
    (by intro w x y; simp [star_add, Finsupp.single_add])]
  have hs (w : List (Bosonize.A08.OscGen M)) (z : ℂ) :
      (Finsupp.single w z).sum (fun v t => Finsupp.single (Bosonize.A08.wordDagger v) (star t)) =
        Finsupp.single (Bosonize.A08.wordDagger w) (star z) :=
    Finsupp.sum_single_index (by simp)
  simp only [hs, star_star, hword]
  simp

theorem oscSyntaxDagger_mul_contract {M : ℕ} (a b : OscSyntax M) :
    oscSyntaxDagger (a * b) = oscSyntaxDagger b * oscSyntaxDagger a := by
  classical
  have hzero : oscSyntaxDagger (0 : OscSyntax M) = 0 := by simp [oscSyntaxDagger]
  have hadd (x y : OscSyntax M) :
      oscSyntaxDagger (x + y) = oscSyntaxDagger x + oscSyntaxDagger y := by
    simp only [oscSyntaxDagger, MonoidAlgebra.coeff_add]
    rw [Finsupp.sum_add_index' (by intro w; simp)
      (by intro w z t; simp [star_add, Finsupp.single_add])]
    exact MonoidAlgebra.ofCoeff_add _ _
  have hsingle (w : List (Bosonize.A08.OscGen M)) (z : ℂ) :
      oscSyntaxDagger (MonoidAlgebra.single w z) =
        MonoidAlgebra.single (Bosonize.A08.wordDagger w) (star z) := by
    simp [oscSyntaxDagger]
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp [hzero]
  | add x y hx hy => rw [add_mul, hadd, hx, hy, hadd, mul_add]
  | single w z =>
      induction b using MonoidAlgebra.induction_linear with
      | zero => simp [hzero]
      | add x y hx hy => rw [mul_add, hadd, hx, hy, hadd, add_mul]
      | single v t =>
          simp only [MonoidAlgebra.single_mul_single, hsingle]
          change MonoidAlgebra.single (Bosonize.A08.wordDagger (w ++ v)) (star (z * t)) =
            MonoidAlgebra.single (Bosonize.A08.wordDagger v ++ Bosonize.A08.wordDagger w)
              (star t * star z)
          simp [Bosonize.A08.wordDagger, mul_comm]

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
      (jointCoeffAction hp a).comp (jointCoeffAction hp b) := by
  rcases a with ⟨a, x⟩
  rcases b with ⟨b, y⟩
  apply TensorProduct.ext'
  intro v p
  simp only [jointCoeffAction, vertexCoeffMul, TensorProduct.map_tmul,
    LinearMap.comp_apply, oscSyntaxEval_mul_contract, map_mul,
    Module.End.mul_apply]
  change TensorProduct.tmul ℂ (chargeWordAction (ChargeWord.comp a b) v) _ =
    TensorProduct.tmul ℂ (chargeWordAction a (chargeWordAction b v)) _
  rw [chargeWord_comp_action_contract]

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
      jointPairing v (jointCoeffAction hp (vertexCoeffAdjoint a) u) := by
  classical
  rcases a with ⟨f, s⟩
  have hosc (a : OscSyntax M) (p q : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M p
        (Bosonize.A08.oscRep M (Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (oscSyntaxEval a)) q) =
      Bosonize.A08.oscPairing M
        (Bosonize.A08.oscRep M (Bosonize.A08.bogoliubovMap M hp.c (-hp.s)
          (oscSyntaxEval (oscSyntaxDagger a))) p) q := by
    classical
    have padd (r s t : Bosonize.A08.OscPoly M) :
        Bosonize.A08.oscPairing M r (s + t) =
          Bosonize.A08.oscPairing M r s + Bosonize.A08.oscPairing M r t := by
      simp only [Bosonize.A08.oscPairing, map_add, mul_add, Finset.sum_add_distrib]
    have psmul (z : ℂ) (r s : Bosonize.A08.OscPoly M) :
        Bosonize.A08.oscPairing M r (z • s) = z * Bosonize.A08.oscPairing M r s := by
      simp only [Bosonize.A08.oscPairing, map_smul, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have paddleft (r s t : Bosonize.A08.OscPoly M) :
        Bosonize.A08.oscPairing M (r + s) t =
          Bosonize.A08.oscPairing M r t + Bosonize.A08.oscPairing M s t := by
      rw [← Bosonize.A08.oscPairing_conj, padd, star_add,
        Bosonize.A08.oscPairing_conj, Bosonize.A08.oscPairing_conj]
    have psmulleft (z : ℂ) (r s : Bosonize.A08.OscPoly M) :
        Bosonize.A08.oscPairing M (z • r) s = star z * Bosonize.A08.oscPairing M r s := by
      rw [← Bosonize.A08.oscPairing_conj, psmul, star_mul, Bosonize.A08.oscPairing_conj, mul_comm]
    have dadd (x y : OscSyntax M) :
        oscSyntaxDagger (x + y) = oscSyntaxDagger x + oscSyntaxDagger y := by
      simp only [oscSyntaxDagger, MonoidAlgebra.coeff_add]
      rw [Finsupp.sum_add_index' (by intro w; simp)
        (by intro w z t; simp [star_add, Finsupp.single_add])]
      exact MonoidAlgebra.ofCoeff_add _ _
    have dsingle (w : List (Bosonize.A08.OscGen M)) (z : ℂ) :
        oscSyntaxDagger (MonoidAlgebra.single w z) =
          MonoidAlgebra.single (Bosonize.A08.wordDagger w) (star z) := by
      simp [oscSyntaxDagger]
    have eadd (x y : OscSyntax M) : oscSyntaxEval (x + y) = oscSyntaxEval x + oscSyntaxEval y := by
      simp only [oscSyntaxEval, MonoidAlgebra.coeff_add]
      exact Finsupp.sum_add_index' (by intro w; simp) (by intro w z t; simp [add_smul])
    have esingle (w : List (Bosonize.A08.OscGen M)) (z : ℂ) :
        oscSyntaxEval (MonoidAlgebra.single w z) = z • Bosonize.A08.wordElement M w := by
      simp [oscSyntaxEval]
    have hword (w : List (Bosonize.A08.OscGen M)) :
        Bosonize.A08.wordDagger (Bosonize.A08.wordDagger w) = w := by
      simp [Bosonize.A08.wordDagger, List.map_reverse, List.map_map, Function.comp_def]
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp [oscSyntaxDagger, oscSyntaxEval, Bosonize.A08.oscPairing]
    | add x y hx hy =>
        simp only [dadd, eadd, map_add, LinearMap.add_apply, padd, paddleft]
        rw [hx, hy]
    | single w z =>
        rw [dsingle, esingle, esingle]
        simp only [map_smul, LinearMap.smul_apply, psmul, psmulleft, star_star]
        congr 1
        simpa only [hword] using
          Bosonize.A08.bogoliubovMap_word_adjoint M hp.c (-hp.s)
            (Bosonize.A08.wordDagger w) p q
  let b := jointBasisOf M
  have hleft (r s : JointCarrier M) : jointPairing r s =
      ∑ i ∈ (b.repr r).support, star (b.repr r i) * jointBasisWeight i * b.repr s i := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro i _ hi
    simp [Finsupp.notMem_support_iff.mp hi]
  have hright (r s : JointCarrier M) : jointPairing r s =
      ∑ i ∈ (b.repr s).support, star (b.repr r i) * jointBasisWeight i * b.repr s i := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro i _ hi
    simp [Finsupp.notMem_support_iff.mp hi]
  have paddright (r s t : JointCarrier M) : jointPairing r (s + t) =
      jointPairing r s + jointPairing r t := by
    simp only [hleft, map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]
  have paddleft (r s t : JointCarrier M) : jointPairing (r + s) t =
      jointPairing r t + jointPairing s t := by
    simp only [hright, map_add, Finsupp.add_apply, star_add, add_mul, Finset.sum_add_distrib]
  induction v using TensorProduct.inductionOn with
  | add v w hv hw =>
      simp only [map_add, paddleft, hv, hw]
  | tmul v p =>
      induction u using TensorProduct.inductionOn with
      | add u w hu hw => simp only [map_add, paddright, hu, hw]
      | tmul u q =>
          simp only [jointCoeffAction, vertexCoeffAdjoint, TensorProduct.map_tmul,
            jointPairing_tmul_factor_contract, chargeWordActionLinear]
          change chargePairing (chargeWordAction f v) u * _ =
            chargePairing v (chargeWordAction (ChargeWord.adjoint f) u) * _
          rw [chargeWord_adjoint_pairing_contract]
          congr 1
          simpa only [oscSyntaxDagger_involutive_contract] using
            (hosc (oscSyntaxDagger s) p q).symm

theorem jointCoeffFunctional_is_matrix_coefficient_contract {M : ℕ}
    (hp : Bosonize.Ch18.HyperbolicPair) (N : Charge) (a : vertexCoeff M) :
    jointCoeffFunctional hp N a =
      jointPairing (jointBasis M N) (jointCoeffAction hp a (jointBasis M N)) := by
  classical
  have hcharge (v : ChargeVec) : chargePairing (Finsupp.single N 1) v = v N := by
    simp [chargePairing, Finsupp.single_apply]
  have hosc (p : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M 1 p = MvPolynomial.lcoeff ℂ 0 p := by
    simp [Bosonize.A08.oscPairing, Bosonize.A08.oscMonomialNorm]
  simp only [jointCoeffFunctional, jointCoeffAction, jointBasis,
    TensorProduct.map_tmul, jointTensorFunctional_tmul,
    jointPairing_tmul_factor_contract, hcharge, hosc]

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
      star (jointCoeffFunctional hp N a) := by
  classical
  have hconj (v u : JointCarrier M) : star (jointPairing v u) = jointPairing u v := by
    unfold jointPairing
    simp only [star_sum, star_mul, star_star]
    rw [Finset.union_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [jointBasisWeight, star_natCast]
    ring
  rw [jointCoeffFunctional_is_matrix_coefficient_contract,
    jointCoeffFunctional_is_matrix_coefficient_contract,
    ← jointCoeffAction_adjoint_pairing_contract]
  exact (hconj _ _).symm

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




/-! The following contracts are intentionally Phase A placeholders. -/

theorem chargeGauge_unitary_contract (h : ℕ) (N : Charge) :
    ‖chargeGauge h N‖ = 1 := by
  simp [chargeGauge]

theorem gauge_adapter_right_contract (h : ℕ) (N : Charge) :
    chargeGauge h (chargeShiftR N) / chargeGauge h N =
      (-1 : ℂ) ^ (h + N.1 - 1) := by
  have hdiff : chargeGaugeExponent h (chargeShiftR N) - chargeGaugeExponent h N =
      -((h : ℤ) + N.1 - 1) := by
    have hp : (N.1 - 1) * (N.1 - 1 - 1) = N.1 * (N.1 - 1) - 2 * (N.1 - 1) := by ring
    unfold chargeGaugeExponent chargeShiftR
    dsimp
    have hlin : (h : ℤ) * (N.1 - 1) = (h : ℤ) * N.1 - h := by ring
    rw [hp, hlin]
    omega
  unfold chargeGauge
  rw [← zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0), hdiff, zpow_neg]
  rw [← inv_zpow]
  norm_num

theorem gauge_adapter_left_contract (h : ℕ) (N : Charge) :
    chargeGauge h (chargeShiftL N) / chargeGauge h N =
      (-1 : ℂ) ^ (N.2 - 1) := by
  have hdiff : chargeGaugeExponent h (chargeShiftL N) - chargeGaugeExponent h N =
      -(N.2 - 1) := by
    have hp : (N.2 - 1) * (N.2 - 1 - 1) = N.2 * (N.2 - 1) - 2 * (N.2 - 1) := by ring
    unfold chargeGaugeExponent chargeShiftL
    dsimp
    rw [hp]
    omega
  unfold chargeGauge
  rw [← zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0), hdiff, zpow_neg, ← inv_zpow]
  norm_num

theorem gauge_adapter_left_klein_contract (h : ℕ) (N : Charge) :
    (-1 : ℂ) ^ N.1 *
        (chargeGauge h (chargeShiftL N) / chargeGauge h N) =
      (-1 : ℂ) ^ (N.1 + N.2 - 1) := by
  rw [gauge_adapter_left_contract, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  congr 1
  omega

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
          (aD N) ((y.val : ℤ) - (x.val : ℤ)) := by
  have hinv : inverseShiftD (chargeShiftDEquiv N) = N := chargeShiftDEquiv.symm_apply_apply N
  have hsign : (-1 : ℂ) ^ N.1 * star ((-1 : ℂ) ^ N.1) = 1 := by
    rw [star_zpow₀, ← mul_zpow]
    norm_num
  change (if chargeShiftDEquiv.symm (chargeShiftDEquiv N) = N then
    ((-1 : ℂ) ^ N.1 * chargePhase L (aD N) y) *
      star ((-1 : ℂ) ^ (inverseShiftD (chargeShiftDEquiv N)).1 *
        chargePhase L (aD (inverseShiftD (chargeShiftDEquiv N))) x) else 0) = _
  rw [chargeShiftDEquiv.symm_apply_apply, hinv]
  simp only [ite_true, eq_self, star_mul]
  calc
    _ = ((-1 : ℂ) ^ N.1 * star ((-1 : ℂ) ^ N.1)) *
        (chargePhase L (aD N) y * star (chargePhase L (aD N) x)) := by ring
    _ = _ := by rw [hsign, one_mul, source_phase_product_contract L _hL (aD N) y x]

theorem charge_selection_S_contract (L : ℕ) (_hL : 0 < L) (x y : Position L) (N : Charge) :
    chargeBasisExpectation N
      (ChargeWord.comp (kleinSAdj L x) (kleinS L y)) =
        Bosonize.A01.integerCharacter (Bosonize.A01.canonicalRoot L)
          (aS N) ((y.val : ℤ) - (x.val : ℤ)) := by
  have hinv : inverseShiftS (chargeShiftSEquiv N) = N := chargeShiftSEquiv.symm_apply_apply N
  have hsign : (-1 : ℂ) ^ N.1 * star ((-1 : ℂ) ^ N.1) = 1 := by
    rw [star_zpow₀, ← mul_zpow]
    norm_num
  change (if chargeShiftSEquiv.symm (chargeShiftSEquiv N) = N then
    ((-1 : ℂ) ^ N.1 * chargePhase L (aS N) y) *
      star ((-1 : ℂ) ^ (inverseShiftS (chargeShiftSEquiv N)).1 *
        chargePhase L (aS (inverseShiftS (chargeShiftSEquiv N))) x) else 0) = _
  rw [chargeShiftSEquiv.symm_apply_apply, hinv]
  simp only [ite_true, eq_self, star_mul]
  calc
    _ = ((-1 : ℂ) ^ N.1 * star ((-1 : ℂ) ^ N.1)) *
        (chargePhase L (aS N) y * star (chargePhase L (aS N) x)) := by ring
    _ = _ := by rw [hsign, one_mul, source_phase_product_contract L _hL (aS N) y x]

theorem canonical_charge_selection_D_contract (h : ℕ) (L : ℕ) (_hL : 0 < L)
    (x y : Position L) (N : Charge) :
    chargeBasisExpectation N
      (ChargeWord.comp (canonicalKleinDAdj h L x) (canonicalKleinD h L y)) =
        Bosonize.A01.integerCharacter (Bosonize.A01.canonicalRoot L)
          (aD N) ((y.val : ℤ) - (x.val : ℤ)) := by
  have hinv : inverseShiftD (chargeShiftDEquiv N) = N := chargeShiftDEquiv.symm_apply_apply N
  have hunit (k : ℤ) : (-1 : ℂ) ^ k * star ((-1 : ℂ) ^ k) = 1 := by
    rw [star_zpow₀, ← mul_zpow]
    norm_num
  have hg (K : Charge) : chargeGauge h K * star (chargeGauge h K) = 1 := hunit _
  change (if chargeShiftDEquiv.symm (chargeShiftDEquiv N) = N then
    (chargeGauge h (chargeShiftD N) * ((-1 : ℂ) ^ N.1 * chargePhase L (aD N) y) *
      star (chargeGauge h N)) *
    star (chargeGauge h (chargeShiftD (inverseShiftD (chargeShiftDEquiv N))) *
      ((-1 : ℂ) ^ (inverseShiftD (chargeShiftDEquiv N)).1 *
        chargePhase L (aD (inverseShiftD (chargeShiftDEquiv N))) x) *
      star (chargeGauge h (inverseShiftD (chargeShiftDEquiv N)))) else 0) = _
  rw [chargeShiftDEquiv.symm_apply_apply, hinv]
  simp only [ite_true, eq_self, star_mul, star_star]
  calc
    _ = (chargeGauge h (chargeShiftD N) * star (chargeGauge h (chargeShiftD N))) *
        (chargeGauge h N * star (chargeGauge h N)) *
        ((-1 : ℂ) ^ N.1 * star ((-1 : ℂ) ^ N.1)) *
        (chargePhase L (aD N) y * star (chargePhase L (aD N) x)) := by ring
    _ = _ := by rw [hg, hg, hunit, one_mul, one_mul, one_mul,
      source_phase_product_contract L _hL (aD N) y x]

theorem canonical_charge_selection_S_contract (h : ℕ) (L : ℕ) (_hL : 0 < L)
    (x y : Position L) (N : Charge) :
    chargeBasisExpectation N
      (ChargeWord.comp (canonicalKleinSAdj h L x) (canonicalKleinS h L y)) =
        Bosonize.A01.integerCharacter (Bosonize.A01.canonicalRoot L)
          (aS N) ((y.val : ℤ) - (x.val : ℤ)) := by
  have hinv : inverseShiftS (chargeShiftSEquiv N) = N := chargeShiftSEquiv.symm_apply_apply N
  have hunit (k : ℤ) : (-1 : ℂ) ^ k * star ((-1 : ℂ) ^ k) = 1 := by
    rw [star_zpow₀, ← mul_zpow]
    norm_num
  have hg (K : Charge) : chargeGauge h K * star (chargeGauge h K) = 1 := hunit _
  change (if chargeShiftSEquiv.symm (chargeShiftSEquiv N) = N then
    (chargeGauge h (chargeShiftS N) * ((-1 : ℂ) ^ N.1 * chargePhase L (aS N) y) *
      star (chargeGauge h N)) *
    star (chargeGauge h (chargeShiftS (inverseShiftS (chargeShiftSEquiv N))) *
      ((-1 : ℂ) ^ (inverseShiftS (chargeShiftSEquiv N)).1 *
        chargePhase L (aS (inverseShiftS (chargeShiftSEquiv N))) x) *
      star (chargeGauge h (inverseShiftS (chargeShiftSEquiv N)))) else 0) = _
  rw [chargeShiftSEquiv.symm_apply_apply, hinv]
  simp only [ite_true, eq_self, star_mul, star_star]
  calc
    _ = (chargeGauge h (chargeShiftS N) * star (chargeGauge h (chargeShiftS N))) *
        (chargeGauge h N * star (chargeGauge h N)) *
        ((-1 : ℂ) ^ N.1 * star ((-1 : ℂ) ^ N.1)) *
        (chargePhase L (aS N) y * star (chargePhase L (aS N) x)) := by ring
    _ = _ := by rw [hg, hg, hunit, one_mul, one_mul, one_mul,
      source_phase_product_contract L _hL (aS N) y x]

theorem same_channel_commutator_contract {M h : ℕ} (_hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (x y : Position (2 * h)) (channel : Bool) :
    Bosonize.V1S1.contraction hp
      (if channel then xSForm (M := M) hp x else xDForm (M := M) hp x)
      (if channel then xSForm (M := M) hp y else xDForm (M := M) hp y) =
    Bosonize.V1S1.contraction hp
      (if channel then xSForm (M := M) hp y else xDForm (M := M) hp y)
      (if channel then xSForm (M := M) hp x else xDForm (M := M) hp x) := by
  classical
  let L := 2 * h
  let : Fintype Bosonize.A06.Orientation :=
    ⟨{Bosonize.A06.Orientation.right, Bosonize.A06.Orientation.left}, by
      intro ν; cases ν <;> simp⟩
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
            ((i.val : ℂ) + 1) else 0) := by
    classical
    cases b <;> cases ν <;> cases μ <;>
      simp [qForm, dressedModeForm, Bosonize.V1S1.dressedGeneratorForm,
        epsilon, Bosonize.A07Interactions.oppositeOrientation, Finsupp.single_apply] <;> ring


  have hfield (hp : Bosonize.Ch18.HyperbolicPair) (x : Position L)
      (channel b : Bool) (ν : Bosonize.A06.Orientation) (i : Fin M) :
      (if channel then xSForm (M := M) hp x else xDForm (M := M) hp x) (b, (ν, i)) =
        (if channel && (ν == Bosonize.A06.Orientation.left) then (-1 : ℂ) else 1) *
        (Bosonize.A01.canonicalRoot L) ^
          ((if b then -(epsilon ν) else epsilon ν) * ((i.val : ℤ) + 1) * (x.val : ℤ)) /
          ((i.val : ℂ) + 1) := by
    have hc : (hp.c : ℂ) ^ 2 - (hp.s : ℂ) ^ 2 = 1 := by exact_mod_cast hp.hyperbolic_id
    cases channel <;> cases b <;> cases ν <;>
      simp [xDForm, xSForm, hq, epsilon,
        Bosonize.A07Interactions.oppositeOrientation] <;>
      ring_nf <;>
      rw [show (hp.c : ℂ) ^ 2 = 1 + (hp.s : ℂ) ^ 2 by linear_combination hc] <;>
      ring
  have hfull (f g : Bosonize.V1S1.OscLinearForm M) :
      Bosonize.V1S1.contraction hp f g =
        ∑ i : Bosonize.A08.OscGen M, ∑ j : Bosonize.A08.OscGen M,
          f i * g j * Bosonize.V1S1.generatorContractionExpected hp i j := by
    rw [Bosonize.V1S1.contraction_coeff_formula]
    have hg (i : Bosonize.A08.OscGen M) :
        (∑ j ∈ g.support, f i * g j * Bosonize.V1S1.generatorContractionExpected hp i j) =
        ∑ j : Bosonize.A08.OscGen M, f i * g j * Bosonize.V1S1.generatorContractionExpected hp i j := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp [Finsupp.notMem_support_iff.mp hj]
    simp_rw [hg]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp [Finsupp.notMem_support_iff.mp hi]
  have hsumO (f : Bosonize.A06.Orientation → ℂ) :
      (∑ ν, f ν) = f .right + f .left := by
    change (∑ ν ∈ ({.right, .left} : Finset Bosonize.A06.Orientation), f ν) = _
    simp
  rw [hfull, hfull]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, hsumO, hfield]
  cases channel <;>
    simp [Bosonize.V1S1.generatorContractionExpected,
      Bosonize.A07Interactions.oppositeOrientation, epsilon, mul_ite] <;>
    simp only [← Finset.sum_add_distrib] <;>
    apply Finset.sum_congr rfl <;> intro i hi <;> ring

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
          (if channel then xSForm (M := M) hp x else xDForm (M := M) hp x)) := by
  classical
  let : Fintype Bosonize.A06.Orientation :=
    ⟨{Bosonize.A06.Orientation.right, Bosonize.A06.Orientation.left}, by
      intro ν; cases ν <;> simp⟩
  let R (g : Bosonize.A08.OscGen M) := Bosonize.A08.oscRep M (FreeAlgebra.ι ℂ g)
  let E := Bosonize.V1S1.generatorContractionExpected (M := M) hp
  have hc : (hp.c : ℂ) ^ 2 = 1 + (hp.s : ℂ) ^ 2 := by
    have hh : (hp.c : ℂ) ^ 2 - (hp.s : ℂ) ^ 2 = 1 := by exact_mod_cast hp.hyperbolic_id
    linear_combination hh
  have haa (p q : Bosonize.A08.OscMode M) :
      Bosonize.A08.oscAnnihilation M p * Bosonize.A08.oscAnnihilation M q -
      Bosonize.A08.oscAnnihilation M q * Bosonize.A08.oscAnnihilation M p = 0 :=
    Bosonize.A08.osc_annihilators_commute M p q
  have hcc (p q : Bosonize.A08.OscMode M) :
      Bosonize.A08.oscCreation M p * Bosonize.A08.oscCreation M q -
      Bosonize.A08.oscCreation M q * Bosonize.A08.oscCreation M p = 0 :=
    Bosonize.A08.osc_creators_commute M p q
  have hac (p q : Bosonize.A08.OscMode M) :
      Bosonize.A08.oscAnnihilation M p * Bosonize.A08.oscCreation M q -
      Bosonize.A08.oscCreation M q * Bosonize.A08.oscAnnihilation M p =
        (if p = q then (Bosonize.A08.oscWeight p : ℂ) else 0) •
          (1 : Module.End ℂ (Bosonize.A08.OscPoly M)) := by
    simpa only [Bosonize.A02.commutator, ite_smul, zero_smul] using Bosonize.A08.osc_ccr M p q
  have hca (p q : Bosonize.A08.OscMode M) :
      Bosonize.A08.oscCreation M p * Bosonize.A08.oscAnnihilation M q -
      Bosonize.A08.oscAnnihilation M q * Bosonize.A08.oscCreation M p =
        -((if q = p then (Bosonize.A08.oscWeight q : ℂ) else 0) •
          (1 : Module.End ℂ (Bosonize.A08.OscPoly M))) := by
    rw [← hac q p]
    abel
  have hkernel (i j : Bosonize.A08.OscGen M) :
      R i * R j - R j * R i = (E i j - E j i) •
        (1 : Module.End ℂ (Bosonize.A08.OscPoly M)) := by
    rcases i with ⟨b, ν, i⟩
    rcases j with ⟨d, μ, j⟩
    cases b <;> cases d <;>
      simp only [R, Bosonize.A08.oscRep, FreeAlgebra.lift_ι_apply, Bool.false_eq_true,
        ite_false, ite_true] <;>
      first | rw [haa] | rw [hac] | rw [hca] | rw [hcc]
    all_goals
      cases ν <;> cases μ
      all_goals
        by_cases hij : i = j
        · subst j
          simp [E, Bosonize.V1S1.generatorContractionExpected,
            Bosonize.A07Interactions.oppositeOrientation, Bosonize.A08.oscWeight, hc] <;> module
        · simp [E, Bosonize.V1S1.generatorContractionExpected,
            Bosonize.A07Interactions.oppositeOrientation, hij, Ne.symm hij]
  have hrep (a : Bosonize.V1S1.OscLinearForm M) :
      Bosonize.A08.oscRep M (Bosonize.V1S1.linearElement a) =
        ∑ g : Bosonize.A08.OscGen M, a g • R g := by
    simp only [Bosonize.V1S1.linearElement, map_sum, map_smul]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro g _ hg
    simp [Finsupp.notMem_support_iff.mp hg]
  have hfull (f g : Bosonize.V1S1.OscLinearForm M) :
      Bosonize.V1S1.contraction hp f g =
        ∑ i : Bosonize.A08.OscGen M, ∑ j : Bosonize.A08.OscGen M,
          f i * g j * E i j := by
    rw [Bosonize.V1S1.contraction_coeff_formula]
    change (∑ i ∈ f.support, ∑ j ∈ g.support, f i * g j * E i j) = _
    have hg (i : Bosonize.A08.OscGen M) :
        (∑ j ∈ g.support, f i * g j * E i j) =
        ∑ j : Bosonize.A08.OscGen M, f i * g j * E i j := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp [Finsupp.notMem_support_iff.mp hj]
    simp_rw [hg]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp [Finsupp.notMem_support_iff.mp hi]
  let f := if channel then xSForm (M := M) hp x else xDForm (M := M) hp x
  let g := if channel then xSForm (M := M) hp y else xDForm (M := M) hp y
  have hprod (a b : Bosonize.V1S1.OscLinearForm M) :
      Bosonize.A08.oscRep M (Bosonize.V1S1.linearElement a) *
      Bosonize.A08.oscRep M (Bosonize.V1S1.linearElement b) =
        ∑ i : Bosonize.A08.OscGen M, ∑ j : Bosonize.A08.OscGen M,
          (a i * b j) • (R i * R j) := by
    simp only [hrep, Finset.sum_mul_sum, smul_mul_smul_comm]
  have hrev : Bosonize.A08.oscRep M (Bosonize.V1S1.linearElement g) *
      Bosonize.A08.oscRep M (Bosonize.V1S1.linearElement f) =
      ∑ i : Bosonize.A08.OscGen M, ∑ j : Bosonize.A08.OscGen M,
        (f i * g j) • (R j * R i) := by
    rw [hprod, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  have hreverse : (∑ i : Bosonize.A08.OscGen M, ∑ j : Bosonize.A08.OscGen M,
      f i * g j * E j i) = Bosonize.V1S1.contraction hp g f := by
    rw [hfull, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hscalar : (∑ i : Bosonize.A08.OscGen M, ∑ j : Bosonize.A08.OscGen M,
      (f i * g j) * (E i j - E j i)) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [← hfull, hreverse, same_channel_commutator_contract _hh hp x y channel, sub_self]
  apply sub_eq_zero.mp
  change Bosonize.A08.oscRep M (Bosonize.V1S1.linearElement f) *
      Bosonize.A08.oscRep M (Bosonize.V1S1.linearElement g) -
      Bosonize.A08.oscRep M (Bosonize.V1S1.linearElement g) *
      Bosonize.A08.oscRep M (Bosonize.V1S1.linearElement f) = 0
  rw [hprod, hrev]
  simp only [← Finset.sum_sub_distrib]
  calc
    _ = ∑ i : Bosonize.A08.OscGen M, ∑ j : Bosonize.A08.OscGen M,
        ((f i * g j) * (E i j - E j i)) • (1 : Module.End ℂ (Bosonize.A08.OscPoly M)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simpa only [smul_sub, smul_smul] using
        congrArg (fun z : Module.End ℂ (Bosonize.A08.OscPoly M) => (f i * g j) • z) (hkernel i j)
    _ = (∑ i : Bosonize.A08.OscGen M, ∑ j : Bosonize.A08.OscGen M,
        (f i * g j) * (E i j - E j i)) • (1 : Module.End ℂ (Bosonize.A08.OscPoly M)) := by
      simp only [Finset.sum_smul]
    _ = 0 := by rw [hscalar, zero_smul]

theorem field_adjoint_on_polynomials_contract {M L : ℕ}
    (hp : Bosonize.Ch18.HyperbolicPair) (x : Position L) (channel : Bool)
    (p q : Bosonize.A08.OscPoly M) :
    Bosonize.A08.oscPairing M p
      (Bosonize.A08.oscRep M (Bosonize.V1S1.linearElement
        (if channel then xSForm (M := M) hp x else xDForm (M := M) hp x)) q) =
    Bosonize.A08.oscPairing M
      (Bosonize.A08.oscRep M (Bosonize.V1S1.linearElement
        (if channel then xSForm (M := M) hp x else xDForm (M := M) hp x)) p) q := by
  classical
  let : Fintype Bosonize.A06.Orientation :=
    ⟨{Bosonize.A06.Orientation.right, Bosonize.A06.Orientation.left}, by
      intro ν; cases ν <;> simp⟩
  have padd (r s t : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M r (s + t) =
        Bosonize.A08.oscPairing M r s + Bosonize.A08.oscPairing M r t := by
    simp only [Bosonize.A08.oscPairing, map_add, mul_add, Finset.sum_add_distrib]
  have psmul (z : ℂ) (r s : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M r (z • s) = z * Bosonize.A08.oscPairing M r s := by
    simp only [Bosonize.A08.oscPairing, map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have paddleft (r s t : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M (r + s) t =
        Bosonize.A08.oscPairing M r t + Bosonize.A08.oscPairing M s t := by
    rw [← Bosonize.A08.oscPairing_conj, padd, star_add,
      Bosonize.A08.oscPairing_conj, Bosonize.A08.oscPairing_conj]
  have psmulleft (z : ℂ) (r s : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M (z • r) s = star z * Bosonize.A08.oscPairing M r s := by
    rw [← Bosonize.A08.oscPairing_conj, psmul, star_mul, Bosonize.A08.oscPairing_conj, mul_comm]
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
  have psumright (t : Finset (Bosonize.A08.OscGen M)) (v : Bosonize.A08.OscGen M → Bosonize.A08.OscPoly M)
      (r : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M r (∑ g ∈ t, v g) = ∑ g ∈ t, Bosonize.A08.oscPairing M r (v g) := by
    simp only [Bosonize.A08.oscPairing, map_sum]
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  have psumleft (t : Finset (Bosonize.A08.OscGen M)) (v : Bosonize.A08.OscGen M → Bosonize.A08.OscPoly M)
      (r : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M (∑ g ∈ t, v g) r = ∑ g ∈ t, Bosonize.A08.oscPairing M (v g) r := by
    rw [← Bosonize.A08.oscPairing_conj, psumright, star_sum]
    apply Finset.sum_congr rfl
    intro g _
    exact Bosonize.A08.oscPairing_conj M r (v g)
  have hroot : (starRingEnd ℂ) (Bosonize.A01.canonicalRoot L) = (Bosonize.A01.canonicalRoot L)⁻¹ := by
    unfold Bosonize.A01.canonicalRoot
    rw [← Complex.exp_neg]
    rw [← Complex.exp_conj]
    congr 1
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
    simp [htwo]
    ring
  let f := if channel then xSForm (M := M) hp x else xDForm (M := M) hp x
  have hherm (g : Bosonize.A08.OscGen M) : star (f g) = f (!g.1, g.2) := by
    rcases g with ⟨b, ν, i⟩
    cases channel <;> cases b <;> cases ν <;>
      simp [f, xDForm, xSForm, hq, epsilon, Bosonize.A07Interactions.oppositeOrientation,
        star_div₀, star_zpow₀, hroot, -zpow_neg, neg_mul] <;> ring <;> simp
  have hrep (a : Bosonize.V1S1.OscLinearForm M) :
      Bosonize.A08.oscRep M (Bosonize.V1S1.linearElement a) =
        ∑ g : Bosonize.A08.OscGen M, a g • Bosonize.A08.oscRep M (FreeAlgebra.ι ℂ g) := by
    simp only [Bosonize.V1S1.linearElement, map_sum, map_smul]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro g _ hg
    simp [Finsupp.notMem_support_iff.mp hg]
  have hgen (g : Bosonize.A08.OscGen M) :
      Bosonize.A08.oscPairing M p (Bosonize.A08.oscRep M (FreeAlgebra.ι ℂ g) q) =
      Bosonize.A08.oscPairing M (Bosonize.A08.oscRep M (FreeAlgebra.ι ℂ (!g.1, g.2)) p) q := by
    simpa [Bosonize.A08.wordElement, Bosonize.A08.wordDagger, Bosonize.A08.bogoliubovMap] using
      Bosonize.A08.bogoliubovMap_word_adjoint M 1 0 [(!g.1, g.2)] p q
  let e : Bosonize.A08.OscGen M ≃ Bosonize.A08.OscGen M :=
    { toFun := fun g => (!g.1, g.2)
      invFun := fun g => (!g.1, g.2)
      left_inv := by intro g; simp
      right_inv := by intro g; simp }
  change Bosonize.A08.oscPairing M p (Bosonize.A08.oscRep M (Bosonize.V1S1.linearElement f) q) =
    Bosonize.A08.oscPairing M (Bosonize.A08.oscRep M (Bosonize.V1S1.linearElement f) p) q
  rw [hrep]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, psumright, psumleft, psmul, psmulleft]
  rw [← Equiv.sum_comp e (fun g => star (f g) *
    Bosonize.A08.oscPairing M (Bosonize.A08.oscRep M (FreeAlgebra.ι ℂ g) p) q)]
  apply Finset.sum_congr rfl
  intro g _
  rw [hgen, hherm]
  simp [e]

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
          (oscSyntaxEval (oscillatorExpWithScalar hp x channel (-Complex.I) n))) p) q := by
  classical
  let L := 2 * h
  let f := if channel then xSForm (M := M) hp x else xDForm (M := M) hp x
  let O := Bosonize.A08.oscRep M (Bosonize.A08.bogoliubovMap M hp.c (-hp.s)
    (Bosonize.V1S1.linearElement f))
  have hO (p q : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M p (O q) = Bosonize.A08.oscPairing M (O p) q := by
    classical
    let : Fintype Bosonize.A06.Orientation :=
      ⟨{Bosonize.A06.Orientation.right, Bosonize.A06.Orientation.left}, by
        intro ν; cases ν <;> simp⟩
    have padd (r s t : Bosonize.A08.OscPoly M) :
        Bosonize.A08.oscPairing M r (s + t) =
          Bosonize.A08.oscPairing M r s + Bosonize.A08.oscPairing M r t := by
      simp only [Bosonize.A08.oscPairing, map_add, mul_add, Finset.sum_add_distrib]
    have psmul (z : ℂ) (r s : Bosonize.A08.OscPoly M) :
        Bosonize.A08.oscPairing M r (z • s) = z * Bosonize.A08.oscPairing M r s := by
      simp only [Bosonize.A08.oscPairing, map_smul, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have paddleft (r s t : Bosonize.A08.OscPoly M) :
        Bosonize.A08.oscPairing M (r + s) t =
          Bosonize.A08.oscPairing M r t + Bosonize.A08.oscPairing M s t := by
      rw [← Bosonize.A08.oscPairing_conj, padd, star_add,
        Bosonize.A08.oscPairing_conj, Bosonize.A08.oscPairing_conj]
    have psmulleft (z : ℂ) (r s : Bosonize.A08.OscPoly M) :
        Bosonize.A08.oscPairing M (z • r) s = star z * Bosonize.A08.oscPairing M r s := by
      rw [← Bosonize.A08.oscPairing_conj, psmul, star_mul, Bosonize.A08.oscPairing_conj, mul_comm]
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
    have psumright (t : Finset (Bosonize.A08.OscGen M)) (v : Bosonize.A08.OscGen M → Bosonize.A08.OscPoly M)
        (r : Bosonize.A08.OscPoly M) :
        Bosonize.A08.oscPairing M r (∑ g ∈ t, v g) = ∑ g ∈ t, Bosonize.A08.oscPairing M r (v g) := by
      simp only [Bosonize.A08.oscPairing, map_sum]
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    have psumleft (t : Finset (Bosonize.A08.OscGen M)) (v : Bosonize.A08.OscGen M → Bosonize.A08.OscPoly M)
        (r : Bosonize.A08.OscPoly M) :
        Bosonize.A08.oscPairing M (∑ g ∈ t, v g) r = ∑ g ∈ t, Bosonize.A08.oscPairing M (v g) r := by
      rw [← Bosonize.A08.oscPairing_conj, psumright, star_sum]
      apply Finset.sum_congr rfl
      intro g _
      exact Bosonize.A08.oscPairing_conj M r (v g)
    have hroot : (starRingEnd ℂ) (Bosonize.A01.canonicalRoot L) = (Bosonize.A01.canonicalRoot L)⁻¹ := by
      unfold Bosonize.A01.canonicalRoot
      rw [← Complex.exp_neg]
      rw [← Complex.exp_conj]
      congr 1
      have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
      simp [htwo]
      ring
    let f := if channel then xSForm (M := M) hp x else xDForm (M := M) hp x
    have hherm (g : Bosonize.A08.OscGen M) : star (f g) = f (!g.1, g.2) := by
      rcases g with ⟨b, ν, i⟩
      cases channel <;> cases b <;> cases ν <;>
        simp [f, xDForm, xSForm, hq, epsilon, Bosonize.A07Interactions.oppositeOrientation,
          star_div₀, star_zpow₀, hroot, -zpow_neg, neg_mul] <;> ring <;> simp
    have hrep (a : Bosonize.V1S1.OscLinearForm M) :
        Bosonize.A08.oscRep M (Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (Bosonize.V1S1.linearElement a)) =
          ∑ g : Bosonize.A08.OscGen M, a g • Bosonize.A08.oscRep M (Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (FreeAlgebra.ι ℂ g)) := by
      simp only [Bosonize.V1S1.linearElement, map_sum, map_smul]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro g _ hg
      simp [Finsupp.notMem_support_iff.mp hg]
    have hgen (g : Bosonize.A08.OscGen M) :
        Bosonize.A08.oscPairing M p (Bosonize.A08.oscRep M (Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (FreeAlgebra.ι ℂ g)) q) =
        Bosonize.A08.oscPairing M (Bosonize.A08.oscRep M (Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (FreeAlgebra.ι ℂ (!g.1, g.2))) p) q := by
      simpa [Bosonize.A08.wordElement, Bosonize.A08.wordDagger] using
        Bosonize.A08.bogoliubovMap_word_adjoint M hp.c (-hp.s) [(!g.1, g.2)] p q
    let e : Bosonize.A08.OscGen M ≃ Bosonize.A08.OscGen M :=
      { toFun := fun g => (!g.1, g.2)
        invFun := fun g => (!g.1, g.2)
        left_inv := by intro g; simp
        right_inv := by intro g; simp }
    change Bosonize.A08.oscPairing M p (Bosonize.A08.oscRep M (Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (Bosonize.V1S1.linearElement f)) q) =
      Bosonize.A08.oscPairing M (Bosonize.A08.oscRep M (Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (Bosonize.V1S1.linearElement f)) p) q
    rw [hrep]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, psumright, psumleft, psmul, psmulleft]
    rw [← Equiv.sum_comp e (fun g => star (f g) *
      Bosonize.A08.oscPairing M (Bosonize.A08.oscRep M (Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (FreeAlgebra.ι ℂ g)) p) q)]
    apply Finset.sum_congr rfl
    intro g _
    rw [hgen, hherm]
    simp [e]
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
  let evalHom := MonoidAlgebra.lift ℂ (Bosonize.A08.OscAlgebra M)
    (List (Bosonize.A08.OscGen M)) wordMap
  have heval (x : OscSyntax M) : oscSyntaxEval x = evalHom x := by
    simp [oscSyntaxEval, evalHom, MonoidAlgebra.lift_apply, wordMap]
  have padd (r s t : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M r (s + t) =
        Bosonize.A08.oscPairing M r s + Bosonize.A08.oscPairing M r t := by
    simp only [Bosonize.A08.oscPairing, map_add, mul_add, Finset.sum_add_distrib]
  have psmul (z : ℂ) (r s : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M r (z • s) = z * Bosonize.A08.oscPairing M r s := by
    simp only [Bosonize.A08.oscPairing, map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have paddleft (r s t : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M (r + s) t =
        Bosonize.A08.oscPairing M r t + Bosonize.A08.oscPairing M s t := by
    rw [← Bosonize.A08.oscPairing_conj, padd, star_add,
      Bosonize.A08.oscPairing_conj, Bosonize.A08.oscPairing_conj]
  have psmulleft (z : ℂ) (r s : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M (z • r) s = star z * Bosonize.A08.oscPairing M r s := by
    rw [← Bosonize.A08.oscPairing_conj, psmul, star_mul, Bosonize.A08.oscPairing_conj, mul_comm]
  have hseries (ι : ℂ) (k : ℕ) :
      Bosonize.A08.oscRep M (Bosonize.A08.bogoliubovMap M hp.c (-hp.s)
        (oscSyntaxEval (oscillatorExpWithScalar hp x channel ι k))) =
      (((k.factorial : ℂ)⁻¹) * ι ^ k) • O ^ k := by
    simp only [oscillatorExpWithScalar, heval, map_smul, map_pow]
    rw [← heval, oscSyntax_roundtrip_freeAlgebra_contract]
    simp only [smul_pow, smul_smul]
    rfl
  have hpowers (k : ℕ) (p q : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M p ((O ^ k) q) =
      Bosonize.A08.oscPairing M ((O ^ k) p) q := by
    induction k generalizing p q with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, hO, ih]
        rw [← Module.End.mul_apply, ← pow_succ, pow_succ']
  unfold oscillatorExp
  rw [hseries, hseries]
  simp only [LinearMap.smul_apply, psmul, psmulleft]
  rw [hpowers]
  have hI : star (-Complex.I) = Complex.I := by simp
  simp only [star_mul, star_inv₀, star_natCast, star_pow, hI]
  ring

theorem oscillator_syntax_dagger_inverse_pullback_represents_adjoint_contract {M : ℕ}
    (hp : Bosonize.Ch18.HyperbolicPair)
    (a : OscSyntax M) (p q : Bosonize.A08.OscPoly M) :
    Bosonize.A08.oscPairing M p
      (Bosonize.A08.oscRep M
        (Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (oscSyntaxEval a)) q) =
    Bosonize.A08.oscPairing M
      (Bosonize.A08.oscRep M
        (Bosonize.A08.bogoliubovMap M hp.c (-hp.s)
          (oscSyntaxEval (oscSyntaxDagger a))) p) q := by
  classical
  have padd (r s t : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M r (s + t) =
        Bosonize.A08.oscPairing M r s + Bosonize.A08.oscPairing M r t := by
    simp only [Bosonize.A08.oscPairing, map_add, mul_add, Finset.sum_add_distrib]
  have psmul (z : ℂ) (r s : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M r (z • s) = z * Bosonize.A08.oscPairing M r s := by
    simp only [Bosonize.A08.oscPairing, map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have paddleft (r s t : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M (r + s) t =
        Bosonize.A08.oscPairing M r t + Bosonize.A08.oscPairing M s t := by
    rw [← Bosonize.A08.oscPairing_conj, padd, star_add,
      Bosonize.A08.oscPairing_conj, Bosonize.A08.oscPairing_conj]
  have psmulleft (z : ℂ) (r s : Bosonize.A08.OscPoly M) :
      Bosonize.A08.oscPairing M (z • r) s = star z * Bosonize.A08.oscPairing M r s := by
    rw [← Bosonize.A08.oscPairing_conj, psmul, star_mul, Bosonize.A08.oscPairing_conj, mul_comm]
  have dadd (x y : OscSyntax M) :
      oscSyntaxDagger (x + y) = oscSyntaxDagger x + oscSyntaxDagger y := by
    simp only [oscSyntaxDagger, MonoidAlgebra.coeff_add]
    rw [Finsupp.sum_add_index' (by intro w; simp)
      (by intro w z t; simp [star_add, Finsupp.single_add])]
    exact MonoidAlgebra.ofCoeff_add _ _
  have dsingle (w : List (Bosonize.A08.OscGen M)) (z : ℂ) :
      oscSyntaxDagger (MonoidAlgebra.single w z) =
        MonoidAlgebra.single (Bosonize.A08.wordDagger w) (star z) := by
    simp [oscSyntaxDagger]
  have eadd (x y : OscSyntax M) : oscSyntaxEval (x + y) = oscSyntaxEval x + oscSyntaxEval y := by
    simp only [oscSyntaxEval, MonoidAlgebra.coeff_add]
    exact Finsupp.sum_add_index' (by intro w; simp) (by intro w z t; simp [add_smul])
  have esingle (w : List (Bosonize.A08.OscGen M)) (z : ℂ) :
      oscSyntaxEval (MonoidAlgebra.single w z) = z • Bosonize.A08.wordElement M w := by
    simp [oscSyntaxEval]
  have hword (w : List (Bosonize.A08.OscGen M)) :
      Bosonize.A08.wordDagger (Bosonize.A08.wordDagger w) = w := by
    simp [Bosonize.A08.wordDagger, List.map_reverse, List.map_map, Function.comp_def]
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp [oscSyntaxDagger, oscSyntaxEval, Bosonize.A08.oscPairing]
  | add x y hx hy =>
      simp only [dadd, eadd, map_add, LinearMap.add_apply, padd, paddleft]
      rw [hx, hy]
  | single w z =>
      rw [dsingle, esingle, esingle]
      simp only [map_smul, LinearMap.smul_apply, psmul, psmulleft, star_star]
      congr 1
      simpa only [hword] using
        Bosonize.A08.bogoliubovMap_word_adjoint M hp.c (-hp.s)
          (Bosonize.A08.wordDagger w) p q

theorem vertexSeriesAdjoint_reverses_product_contract {M : ℕ}
    (f g : VertexSeries M) :
    vertexSeriesAdjoint (vertexSeriesMul f g) =
      vertexSeriesMul (vertexSeriesAdjoint g) (vertexSeriesAdjoint f) := by
  classical
  have hcharge (a b : ChargeWord) :
      ChargeWord.adjoint (ChargeWord.comp a b) =
        ChargeWord.comp (ChargeWord.adjoint b) (ChargeWord.adjoint a) := by
    cases a with
    | mk aTarget aa =>
      cases b with
      | mk bt ba =>
        simp [ChargeWord.comp, ChargeWord.adjoint, Equiv.trans_apply, star_mul, mul_comm]
  have hcoeff (a b : vertexCoeff M) :
      vertexCoeffAdjoint (vertexCoeffMul a b) =
        vertexCoeffMul (vertexCoeffAdjoint b) (vertexCoeffAdjoint a) := by
    rcases a with ⟨a, x⟩
    rcases b with ⟨b, y⟩
    change (ChargeWord.adjoint (ChargeWord.comp a b), oscSyntaxDagger (x * y)) = _
    rw [hcharge, oscSyntaxDagger_mul_contract]
    rfl
  have hmap (s : Finset ℕ) (v : ℕ → Multiset (vertexCoeff M)) :
      (∑ i ∈ s, v i).map vertexCoeffAdjoint = ∑ i ∈ s, (v i).map vertexCoeffAdjoint := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [Finset.sum_insert hi, ih]
  funext n
  simp only [vertexSeriesAdjoint, vertexSeriesMul, hmap,
    Multiset.map_bind, Multiset.map_map, Multiset.bind_map, Function.comp_def, hcoeff]
  rw [← Finset.sum_range_reflect (fun k =>
    (g k).bind fun b => (f (n - k)).map fun a =>
      vertexCoeffMul (vertexCoeffAdjoint b) (vertexCoeffAdjoint a)) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using Finset.mem_range.mp hk
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hk']
  exact Multiset.bind_map_comm _ _

theorem difference_variance_contract {M h : ℕ} (_hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (x y : Position (2 * h)) (channel : Bool) :
    Bosonize.V1S1.contraction hp
      (if channel then xSForm (M := M) hp y - xSForm (M := M) hp x
        else xDForm (M := M) hp y - xDForm (M := M) hp x)
      (if channel then xSForm (M := M) hp y - xSForm (M := M) hp x
        else xDForm (M := M) hp y - xDForm (M := M) hp x) =
      (4 : ℂ) * (if channel then gainS hp else gainD hp : ℂ) *
        (dirichletCutoff (2 * h) M x y : ℂ) := by
  classical
  let L := 2 * h
  let : Fintype Bosonize.A06.Orientation :=
    ⟨{Bosonize.A06.Orientation.right, Bosonize.A06.Orientation.left}, by
      intro ν; cases ν <;> simp⟩
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
            ((i.val : ℂ) + 1) else 0) := by
    classical
    cases b <;> cases ν <;> cases μ <;>
      simp [qForm, dressedModeForm, Bosonize.V1S1.dressedGeneratorForm,
        epsilon, Bosonize.A07Interactions.oppositeOrientation, Finsupp.single_apply] <;> ring


  have hfield (hp : Bosonize.Ch18.HyperbolicPair) (x : Position L)
      (channel b : Bool) (ν : Bosonize.A06.Orientation) (i : Fin M) :
      (if channel then xSForm (M := M) hp x else xDForm (M := M) hp x) (b, (ν, i)) =
        (if channel && (ν == Bosonize.A06.Orientation.left) then (-1 : ℂ) else 1) *
        (Bosonize.A01.canonicalRoot L) ^
          ((if b then -(epsilon ν) else epsilon ν) * ((i.val : ℤ) + 1) * (x.val : ℤ)) /
          ((i.val : ℂ) + 1) := by
    have hc : (hp.c : ℂ) ^ 2 - (hp.s : ℂ) ^ 2 = 1 := by exact_mod_cast hp.hyperbolic_id
    cases channel <;> cases b <;> cases ν <;>
      simp [xDForm, xSForm, hq, epsilon,
        Bosonize.A07Interactions.oppositeOrientation] <;>
      ring_nf <;>
      rw [show (hp.c : ℂ) ^ 2 = 1 + (hp.s : ℂ) ^ 2 by linear_combination hc] <;>
      ring
  have hfull (f g : Bosonize.V1S1.OscLinearForm M) :
      Bosonize.V1S1.contraction hp f g =
        ∑ i : Bosonize.A08.OscGen M, ∑ j : Bosonize.A08.OscGen M,
          f i * g j * Bosonize.V1S1.generatorContractionExpected hp i j := by
    rw [Bosonize.V1S1.contraction_coeff_formula]
    have hg (i : Bosonize.A08.OscGen M) :
        (∑ j ∈ g.support, f i * g j * Bosonize.V1S1.generatorContractionExpected hp i j) =
        ∑ j : Bosonize.A08.OscGen M, f i * g j * Bosonize.V1S1.generatorContractionExpected hp i j := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp [Finsupp.notMem_support_iff.mp hj]
    simp_rw [hg]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp [Finsupp.notMem_support_iff.mp hi]
  have hsumO (f : Bosonize.A06.Orientation → ℂ) :
      (∑ ν, f ν) = f .right + f .left := by
    change (∑ ν ∈ ({.right, .left} : Finset Bosonize.A06.Orientation), f ν) = _
    simp
  let F (z : Position (2 * h)) := if channel then xSForm (M := M) hp z else xDForm (M := M) hp z
  let ζ := Bosonize.A01.canonicalRoot (2 * h)
  let a (i : Fin M) (z : Position (2 * h)) : ℤ := ((i.val : ℤ) + 1) * (z.val : ℤ)
  have hdiff : (if channel then xSForm (M := M) hp y - xSForm (M := M) hp x
      else xDForm (M := M) hp y - xDForm (M := M) hp x) = F y - F x := by
    cases channel <;> rfl
  have hsymbolic : Bosonize.V1S1.contraction hp (F y - F x) (F y - F x) =
      (2 : ℂ) * (if channel then gainS hp else gainD hp : ℂ) *
        ∑ i : Fin M, ((ζ ^ (a i y) - ζ ^ (a i x)) *
          (ζ ^ (-(a i y)) - ζ ^ (-(a i x)))) / ((i.val : ℂ) + 1) := by
    rw [hfull]
    simp only [F, Fintype.sum_prod_type, Fintype.sum_bool, hsumO, Finsupp.sub_apply, hfield]
    cases channel <;>
      simp [Bosonize.V1S1.generatorContractionExpected,
        Bosonize.A07Interactions.oppositeOrientation, epsilon, mul_ite, gainD, gainS, -zpow_neg] <;>
      rw [Finset.mul_sum] <;>
      simp only [← Finset.sum_add_distrib] <;>
      apply Finset.sum_congr rfl <;> intro i hi
    all_goals
      have hm : (i.val : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i.val
      simp only [ζ, a, L]
      field_simp [hm]
      ring
  rw [hdiff, hsymbolic]
  have hcos (L : ℕ) (n : ℤ) :
      (Bosonize.A01.canonicalRoot L) ^ n +
        (Bosonize.A01.canonicalRoot L) ^ (-n) =
        2 * (Real.cos (2 * Real.pi * (n : ℝ) / (L : ℝ)) : ℂ) := by
    have hexp (a : ℝ) : Complex.exp ((a : ℂ) * Complex.I) +
        Complex.exp (-((a : ℂ) * Complex.I)) = 2 * (Real.cos a : ℂ) := by
      rw [show -((a : ℂ) * Complex.I) = ((-a : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [Complex.exp_mul_I, Complex.exp_mul_I]
      simp
      ring
    simp only [Bosonize.A01.canonicalRoot, ← Complex.exp_int_mul]
    convert hexp (2 * Real.pi * (n : ℝ) / (L : ℝ)) using 2 <;> push_cast <;> ring
  have hne : ζ ≠ 0 := Complex.exp_ne_zero _
  have hcross (u v : ℤ) : (ζ ^ v - ζ ^ u) * (ζ ^ (-v) - ζ ^ (-u)) =
      2 * (1 - (Real.cos (2 * Real.pi * ((u - v : ℤ) : ℝ) / ((2 * h : ℕ) : ℝ)) : ℂ)) := by
    have hp (r t : ℤ) : ζ ^ r * ζ ^ t = ζ ^ (r + t) := (zpow_add₀ hne r t).symm
    have hsame (r : ℤ) : ζ ^ r * ζ ^ (-r) = 1 := by rw [hp]; simp
    have hxy : ζ ^ u * ζ ^ (-v) = ζ ^ (u - v) := by rw [hp]; rfl
    have hyx : ζ ^ v * ζ ^ (-u) = ζ ^ (-(u - v)) := by rw [hp]; congr 1; ring
    calc
      _ = 2 - (ζ ^ (u - v) + ζ ^ (-(u - v))) := by
        linear_combination (hsame u) + (hsame v) - hxy - hyx
      _ = _ := by rw [hcos]; ring
  have hcut : (dirichletCutoff (2 * h) M x y : ℂ) =
      ∑ i : Fin M, ((1 - Real.cos (2 * Real.pi * ((i.val : ℝ) + 1) *
        ((x.val : ℤ) - (y.val : ℤ)) / ((2 * h : ℕ) : ℝ))) / ((i.val : ℝ) + 1) : ℝ) := by
    unfold dirichletCutoff
    push_cast
    symm
    apply Finset.sum_bij (fun i _ => i.val + 1)
    · intro i _
      simp only [Finset.mem_Icc]
      omega
    · intro i _ j _ hij
      apply Fin.ext
      omega
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      exact ⟨⟨n - 1, by omega⟩, Finset.mem_univ _, by change n - 1 + 1 = n; omega⟩
    · intro i _
      simp
  have hsumvar : (∑ i : Fin M, ((ζ ^ (a i y) - ζ ^ (a i x)) *
      (ζ ^ (-(a i y)) - ζ ^ (-(a i x)))) / ((i.val : ℂ) + 1)) =
      2 * (dirichletCutoff (2 * h) M x y : ℂ) := by
    rw [hcut]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcross]
    have hangle : (2 * Real.pi * (((a i x - a i y : ℤ) : ℝ)) / ((2 * h : ℕ) : ℝ)) =
        2 * Real.pi * ((i.val : ℝ) + 1) * ((x.val : ℤ) - (y.val : ℤ)) / ((2 * h : ℕ) : ℝ) := by
      simp only [a, Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one]
      ring
    rw [hangle]
    push_cast
    ring
  rw [hsumvar]
  ring

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

end Bosonize.V1S2
