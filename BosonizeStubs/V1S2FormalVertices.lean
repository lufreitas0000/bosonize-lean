import Bosonize.Core.V1S1OrderedWick

/-!
# V1-S2: charge words and coefficientwise formal vertices

All oscillator products in this module are interpreted through A08's
polynomial representation.  The free algebra remains the syntax carrier;
the theorem contracts below establish the representation and moment
identities without asserting CCR equalities in that free algebra.
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




/-! Gauge, phase, field and formal-correlator contracts. -/

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
        expectedWeylCorrelator (M := M) hh hp N x y channel := by
  classical
  have contextual_binomial_coefficient {A : Type} [Ring A] (ω : A →+ ℂ) (X Y : A)
      (hctx : ∀ u v, ω (u * (X * Y) * v) = ω (u * (Y * X) * v)) (n : ℕ) :
      ω ((Y - X) ^ n) = ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℂ) * (-1 : ℂ) ^ k * ω (X ^ k * Y ^ (n - k)) := by
    classical
    let c : RingCon A :=
      { r := fun a b => ∀ u v, ω (u * a * v) = ω (u * b * v)
        iseqv :=
          ⟨(by intro a u v; rfl),
            (by intro a b hab u v; exact (hab u v).symm),
            (by intro a b d hab hbd u v; exact (hab u v).trans (hbd u v))⟩
        add' := by
          intro a b d e hab hde u v
          simp only [mul_add, add_mul, map_add]
          rw [hab, hde]
        mul' := by
          intro a b d e hab hde u v
          simpa only [mul_assoc] using
            (hab u (d * v)).trans (by simpa only [mul_assoc] using hde (u * b) v) }
    let ωq : c.Quotient →+ ℂ :=
      { toFun := Quotient.lift (fun a => ω a) (by
          intro a b hab
          simpa using hab 1 1)
        map_zero' := ω.map_zero
        map_add' := by
          intro a b
          refine Quotient.inductionOn₂ a b ?_
          intro a b
          exact ω.map_add a b }
    let q := c.mk'
    have hcomm : Commute (q X) (q Y) := by
      change q X * q Y = q Y * q X
      rw [← map_mul, ← map_mul]
      exact (RingCon.eq c).mpr hctx
    have hterm (k : ℕ) :
        ωq ((-q X) ^ k * (q Y) ^ (n - k) * (n.choose k : c.Quotient)) =
          (n.choose k : ℂ) * (-1 : ℂ) ^ k * ω (X ^ k * Y ^ (n - k)) := by
      rw [← nsmul_eq_mul', map_nsmul]
      have he : (-q X) ^ k * (q Y) ^ (n - k) =
          ((-1 : ℤ) ^ k) • q (X ^ k * Y ^ (n - k)) := by
        rw [neg_pow]
        simp [zsmul_eq_mul, map_mul, map_pow, mul_assoc]
      rw [he, map_zsmul]
      change (n.choose k) • (((-1 : ℤ) ^ k) • ω (X ^ k * Y ^ (n - k))) = _
      simp [nsmul_eq_mul, zsmul_eq_mul, mul_assoc]
    have hbin := congrArg ωq (hcomm.neg_left.add_pow n)
    have hl : (-q X + q Y) ^ n = q ((Y - X) ^ n) := by
      rw [map_pow, map_sub]
      congr 1
      abel
    rw [hl, map_sum] at hbin
    simp_rw [hterm] at hbin
    exact hbin
  have contextual_linear_commute {M : ℕ} (hp : Bosonize.Ch18.HyperbolicPair)
      (f g : Bosonize.V1S1.OscLinearForm M)
      (hfg : Bosonize.V1S1.contraction hp f g = Bosonize.V1S1.contraction hp g f)
      (a b : Bosonize.A08.OscAlgebra M) :
      Bosonize.A08.omegaP M hp (a * (Bosonize.V1S1.linearElement f * Bosonize.V1S1.linearElement g) * b) =
      Bosonize.A08.omegaP M hp (a * (Bosonize.V1S1.linearElement g * Bosonize.V1S1.linearElement f) * b) := by
    classical
    let : Fintype Bosonize.A06.Orientation :=
      ⟨{Bosonize.A06.Orientation.right, Bosonize.A06.Orientation.left}, by
        intro ν; cases ν <;> simp⟩
    let G (i : Bosonize.A08.OscGen M) := FreeAlgebra.ι ℂ i
    let E := Bosonize.V1S1.generatorContractionExpected (M := M) hp
    let ω := Bosonize.A08.omegaP M hp
    have hc : (hp.c : ℂ) ^ 2 = 1 + (hp.s : ℂ) ^ 2 := by
      have H : (hp.c : ℂ) ^ 2 - (hp.s : ℂ) ^ 2 = 1 := by exact_mod_cast hp.hyperbolic_id
      linear_combination H
    have haa (p q : Bosonize.A08.OscMode M) :
        ω (a * (G (false,p) * G (false,q) - G (false,q) * G (false,p)) * b) = 0 :=
      Bosonize.A08.omegaP_ccr_descends_aa M hp a b p q
    have hcc (p q : Bosonize.A08.OscMode M) :
        ω (a * (G (true,p) * G (true,q) - G (true,q) * G (true,p)) * b) = 0 :=
      Bosonize.A08.omegaP_ccr_descends_cc M hp a b p q
    have hac (p q : Bosonize.A08.OscMode M) :
        ω (a * (G (false,p) * G (true,q) - G (true,q) * G (false,p)) * b) =
        (if p = q then (Bosonize.A08.oscWeight p : ℂ) else 0) * ω (a * b) := by
      have H := Bosonize.A08.omegaP_ccr_descends M hp a b p q
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one,
        map_sub, map_smul, smul_eq_mul] at H
      simpa only [G, ω, mul_sub, sub_mul, map_sub] using (sub_eq_zero.mp H)
    have hca (p q : Bosonize.A08.OscMode M) :
        ω (a * (G (true,p) * G (false,q) - G (false,q) * G (true,p)) * b) =
        -((if q = p then (Bosonize.A08.oscWeight q : ℂ) else 0) * ω (a * b)) := by
      have H : G (true,p) * G (false,q) - G (false,q) * G (true,p) =
          -(G (false,q) * G (true,p) - G (true,p) * G (false,q)) := by abel
      rw [H, mul_neg, neg_mul, map_neg, hac]
    have hkernel (i j : Bosonize.A08.OscGen M) :
        ω (a * (G i * G j - G j * G i) * b) = (E i j - E j i) * ω (a * b) := by
      rcases i with ⟨bi, ν, i⟩
      rcases j with ⟨bj, μ, j⟩
      cases bi <;> cases bj <;>
        first | rw [haa] | rw [hac] | rw [hca] | rw [hcc]
      all_goals
        cases ν <;> cases μ
        all_goals
          by_cases hij : i = j
          · subst j
            simp [E, Bosonize.V1S1.generatorContractionExpected,
              Bosonize.A07Interactions.oppositeOrientation, Bosonize.A08.oscWeight, hc] <;> ring <;> simp
          · simp [E, Bosonize.V1S1.generatorContractionExpected,
              Bosonize.A07Interactions.oppositeOrientation, hij, Ne.symm hij]
    have hlinear (u : Bosonize.V1S1.OscLinearForm M) :
        Bosonize.V1S1.linearElement u = ∑ i : Bosonize.A08.OscGen M, u i • G i := by
      unfold Bosonize.V1S1.linearElement
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp [Finsupp.notMem_support_iff.mp hi]
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
    have hprod (a b : Bosonize.V1S1.OscLinearForm M) :
        Bosonize.V1S1.linearElement a *
        Bosonize.V1S1.linearElement b =
          ∑ i : Bosonize.A08.OscGen M, ∑ j : Bosonize.A08.OscGen M,
            (a i * b j) • (G i * G j) := by
      simp only [hlinear, Finset.sum_mul_sum, smul_mul_smul_comm]
    have hrev : Bosonize.V1S1.linearElement g *
        Bosonize.V1S1.linearElement f =
        ∑ i : Bosonize.A08.OscGen M, ∑ j : Bosonize.A08.OscGen M,
          (f i * g j) • (G j * G i) := by
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
      rw [← hfull, hreverse, hfg, sub_self]
    have hexpand : Bosonize.V1S1.linearElement f * Bosonize.V1S1.linearElement g -
        Bosonize.V1S1.linearElement g * Bosonize.V1S1.linearElement f =
        ∑ i : Bosonize.A08.OscGen M, ∑ j : Bosonize.A08.OscGen M,
          (f i * g j) • (G i * G j - G j * G i) := by
      rw [hprod, hrev]
      simp only [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact (smul_sub _ _ _).symm
    have H : ω (a * (Bosonize.V1S1.linearElement f * Bosonize.V1S1.linearElement g -
        Bosonize.V1S1.linearElement g * Bosonize.V1S1.linearElement f) * b) = 0 := by
      rw [hexpand]
      simp only [Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm,
        smul_mul_assoc, map_smul, smul_eq_mul, hkernel]
      calc
        _ = (∑ i : Bosonize.A08.OscGen M, ∑ j : Bosonize.A08.OscGen M,
            f i * g j * (E i j - E j i)) * ω (a * b) := by
          simp only [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = 0 := by rw [hscalar, zero_mul]
    rw [mul_sub, sub_mul, map_sub] at H
    exact sub_eq_zero.mp H
  have oscillator_coefficient_product {M h : ℕ} (hh : 0 < h)
      (hp : Bosonize.Ch18.HyperbolicPair) (x y : Position (2 * h))
      (channel : Bool) (k l : ℕ) :
      Bosonize.A08.omegaP M hp (oscSyntaxEval
        (oscSyntaxDagger (oscillatorExp hp x channel k) * oscillatorExp hp y channel l)) =
      (((k.factorial : ℂ)⁻¹) * ((l.factorial : ℂ)⁻¹) * (-Complex.I) ^ k * Complex.I ^ l) *
        Bosonize.A08.omegaP M hp
          ((Bosonize.V1S1.linearElement (if channel then xSForm hp x else xDForm hp x)) ^ k *
            (Bosonize.V1S1.linearElement (if channel then xSForm hp y else xDForm hp y)) ^ l) := by
    classical
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
    let R (a : OscSyntax M) := Bosonize.A08.oscRep M
      (Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (oscSyntaxEval a))
    have hExpEval (z : Position (2 * h)) (ι : ℂ) (n : ℕ) :
        oscSyntaxEval (oscillatorExpWithScalar hp z channel ι n) =
        ((n.factorial : ℂ)⁻¹) • (ι • Bosonize.V1S1.linearElement
          (if channel then xSForm (M := M) hp z else xDForm (M := M) hp z)) ^ n := by
      simp only [oscillatorExpWithScalar, heval, map_smul, map_pow]
      rw [← heval, oscSyntax_roundtrip_freeAlgebra_contract]
    have hm (a : Bosonize.A08.OscAlgebra M) :
        Bosonize.A08.omegaP M hp a = Bosonize.A08.oscPairing M 1
          (Bosonize.A08.oscRep M (Bosonize.A08.bogoliubovMap M hp.c (-hp.s) a) 1) := by
      simp [Bosonize.A08.omegaP, Bosonize.A08.omega0, Bosonize.A08.oscPairing,
        Bosonize.A08.oscMonomialNorm]
    have hmp (a b : OscSyntax M) : Bosonize.A08.omegaP M hp (oscSyntaxEval (a * b)) =
        Bosonize.A08.oscPairing M 1 (R a (R b 1)) := by
      rw [hm]
      simp only [R, oscSyntaxEval_mul_contract, map_mul, Module.End.mul_apply]
    calc
      _ = Bosonize.A08.oscPairing M 1
          (R (oscSyntaxDagger (oscillatorExp hp x channel k)) (R (oscillatorExp hp y channel l) 1)) := hmp _ _
      _ = Bosonize.A08.oscPairing M (R (oscillatorExp hp x channel k) 1)
          (R (oscillatorExp hp y channel l) 1) := by
        simpa only [R, oscSyntaxDagger_involutive_contract] using
          oscillator_syntax_dagger_inverse_pullback_represents_adjoint_contract hp
            (oscSyntaxDagger (oscillatorExp hp x channel k)) 1 (R (oscillatorExp hp y channel l) 1)
      _ = Bosonize.A08.oscPairing M 1
          (R (oscillatorExpWithScalar hp x channel (-Complex.I) k) (R (oscillatorExp hp y channel l) 1)) := by
        simpa only [Bosonize.A08.oscPairing_conj] using
          congrArg star (oscillatorExp_adjoint_coefficient_contract hh hp x channel k
            (R (oscillatorExp hp y channel l) 1) 1)
      _ = Bosonize.A08.omegaP M hp (oscSyntaxEval
          (oscillatorExpWithScalar hp x channel (-Complex.I) k * oscillatorExp hp y channel l)) :=
        (hmp _ _).symm
      _ = _ := by
        simp only [oscSyntaxEval_mul_contract, oscillatorExp, hExpEval, smul_pow,
          smul_mul_smul_comm, map_smul, smul_smul, smul_eq_mul]
        ring
  have gaussian_coefficient {M h : ℕ} (hh : 0 < h) (hp : Bosonize.Ch18.HyperbolicPair)
      (x y : Position (2 * h)) (channel : Bool) (n : ℕ) :
      let f := if channel then xSForm (M := M) hp y - xSForm (M := M) hp x
        else xDForm (M := M) hp y - xDForm (M := M) hp x
      let g : ℂ := if channel then gainS hp else gainD hp
      let d : ℂ := dirichletCutoff (2 * h) M x y
      (Complex.I ^ n / (n.factorial : ℂ)) *
          Bosonize.A08.omegaP M hp (Bosonize.V1S1.linearElement f ^ n) =
        if n % 2 = 0 then (-2 * g * d) ^ (n / 2) / ((n / 2).factorial : ℂ) else 0 := by
    dsimp only
    let f := if channel then xSForm (M := M) hp y - xSForm (M := M) hp x
      else xDForm (M := M) hp y - xDForm (M := M) hp x
    let g : ℂ := if channel then gainS hp else gainD hp
    let d : ℂ := dirichletCutoff (2 * h) M x y
    change (Complex.I ^ n / (n.factorial : ℂ)) *
      Bosonize.A08.omegaP M hp (Bosonize.V1S1.linearElement f ^ n) =
      if n % 2 = 0 then (-2 * g * d) ^ (n / 2) / ((n / 2).factorial : ℂ) else 0
    have hv : Bosonize.V1S1.contraction hp f f = 4 * g * d := difference_variance_contract hh hp x y channel
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨k, hk⟩ := he
      have hn : n = 2 * k := by omega
      clear hk
      subst n
      have hm : (2 * k) % 2 = 0 := by omega
      have hd : (2 * k) / 2 = k := by omega
      rw [hm, hd]
      simp only [ite_true]
      rw [Bosonize.V1S1.omegaP_single_even_moment, hv, pow_mul, Complex.I_sq]
      have hpowers : (-1 : ℂ) ^ k * (4 * g * d) ^ k =
          (2 : ℂ) ^ k * (-2 * g * d) ^ k := by
        rw [← mul_pow, ← mul_pow]
        congr 1
        ring
      have hk0 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      have h2k0 : ((2 * k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * k)
      have ht : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
      push_cast
      field_simp [hk0, h2k0, ht]
      linear_combination hpowers
    · obtain ⟨k, hk⟩ := ho
      have hn : n = 2 * k + 1 := by omega
      clear hk
      subst n
      have hm : (2 * k + 1) % 2 = 1 := by omega
      rw [hm, Bosonize.V1S1.omegaP_single_odd_moment]
      simp
  have oscillator_cauchy_moment {M h : ℕ} (hh : 0 < h)
      (hp : Bosonize.Ch18.HyperbolicPair) (x y : Position (2 * h))
      (channel : Bool) (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1), Bosonize.A08.omegaP M hp (oscSyntaxEval
        (oscSyntaxDagger (oscillatorExp hp x channel k) * oscillatorExp hp y channel (n - k)))) =
      (Complex.I ^ n / (n.factorial : ℂ)) *
        Bosonize.A08.omegaP M hp
          ((Bosonize.V1S1.linearElement (if channel then xSForm hp y - xSForm hp x
            else xDForm hp y - xDForm hp x)) ^ n) := by
    classical
    let fx := if channel then xSForm (M := M) hp x else xDForm (M := M) hp x
    let fy := if channel then xSForm (M := M) hp y else xDForm (M := M) hp y
    let X := Bosonize.V1S1.linearElement fx
    let Y := Bosonize.V1S1.linearElement fy
    let ω := Bosonize.A08.omegaP M hp
    have hctx (a b : Bosonize.A08.OscAlgebra M) :
        ω (a * (X * Y) * b) = ω (a * (Y * X) * b) :=
      contextual_linear_commute hp fx fy (same_channel_commutator_contract hh hp x y channel) a b
    have hbin := contextual_binomial_coefficient (A := Bosonize.A08.OscAlgebra M) ω.toAddMonoidHom X Y hctx n
    have hlin : Bosonize.V1S1.linearElement (if channel then xSForm (M := M) hp y - xSForm (M := M) hp x
        else xDForm (M := M) hp y - xDForm (M := M) hp x) = Y - X := by
      have hdiff : (if channel then xSForm (M := M) hp y - xSForm (M := M) hp x
          else xDForm (M := M) hp y - xDForm (M := M) hp x) = fy - fx := by
        cases channel <;> rfl
      rw [hdiff]
      let L := Finsupp.linearCombination ℂ (fun i : Bosonize.A08.OscGen M => FreeAlgebra.ι ℂ i)
      change L (fy - fx) = L fy - L fx
      exact L.map_sub fy fx
    have hbin' : Bosonize.A08.omegaP M hp ((Y - X) ^ n) =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (-1 : ℂ)^k *
          Bosonize.A08.omegaP M hp (X^k * Y^(n-k)) := hbin
    with_unfolding_all rw [hlin, hbin', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
    rw [oscillator_coefficient_product hh]
    have hden : ((k.factorial : ℂ)⁻¹) * (((n - k).factorial : ℂ)⁻¹) =
        (n.choose k : ℂ) / (n.factorial : ℂ) := by
      rw [Nat.cast_choose ℂ hk']
      have hf (m : ℕ) : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
      field_simp [hf]
    have hphase : (-Complex.I) ^ k * Complex.I ^ (n - k) =
        (-1 : ℂ) ^ k * Complex.I ^ n := by
      rw [neg_pow, mul_assoc, ← pow_add, show k + (n - k) = n by omega]
    change (((k.factorial : ℂ)⁻¹) * (((n-k).factorial : ℂ)⁻¹) * (-Complex.I)^k * Complex.I^(n-k)) *
      ω (X^k * Y^(n-k)) = _
    calc
      _ = ((((k.factorial : ℂ)⁻¹) * (((n-k).factorial : ℂ)⁻¹)) *
          ((-Complex.I)^k * Complex.I^(n-k))) * ω (X^k * Y^(n-k)) := by ring
      _ = ((n.choose k : ℂ) / (n.factorial : ℂ)) *
          ((-1 : ℂ)^k * Complex.I^n) * ω (X^k * Y^(n-k)) := by rw [hden, hphase]
      _ = _ := by ring
  have vertex_charge_coefficient {h : ℕ} (hh : 0 < h) (N : Charge)
      (x y : Position (2 * h)) (channel : Bool) :
      let c : ℂ := (((2 * h : ℕ) : ℂ))⁻¹
      let K := fun z => if channel then canonicalKleinS h (2 * h) z else canonicalKleinD h (2 * h) z
      chargeBasisExpectation N (ChargeWord.comp (ChargeWord.adjoint (ChargeWord.scale c (K x)))
        (ChargeWord.scale c (K y))) =
      c ^ 2 * Bosonize.A01.integerCharacter (Bosonize.A01.canonicalRoot (2 * h))
        (if channel then aS N else aD N) ((y.val : ℤ) - (x.val : ℤ)) := by
    dsimp only
    let c : ℂ := (((2 * h : ℕ) : ℂ))⁻¹
    let K := fun z => if channel then canonicalKleinS h (2 * h) z else canonicalKleinD h (2 * h) z
    have hs : star c = c := by simp [c]
    have hscale (a b : ChargeWord) :
        chargeBasisExpectation N (ChargeWord.comp (ChargeWord.adjoint (ChargeWord.scale c a))
          (ChargeWord.scale c b)) =
        c ^ 2 * chargeBasisExpectation N (ChargeWord.comp (ChargeWord.adjoint a) b) := by
      change (if a.target.symm (b.target N) = N then
        (c * b.amplitude N) * star (c * a.amplitude (a.target.symm (b.target N))) else 0) =
        c ^ 2 * (if a.target.symm (b.target N) = N then
          b.amplitude N * star (a.amplitude (a.target.symm (b.target N))) else 0)
      split_ifs
      · rw [star_mul, hs]; ring
      · ring
    change chargeBasisExpectation N (ChargeWord.comp (ChargeWord.adjoint (ChargeWord.scale c (K x)))
      (ChargeWord.scale c (K y))) = _
    rw [hscale]
    cases channel
    · change c^2 * chargeBasisExpectation N
        (ChargeWord.comp (canonicalKleinDAdj h (2*h) x) (canonicalKleinD h (2*h) y)) = _
      rw [canonical_charge_selection_D_contract h (2*h) (by omega)]
      rfl
    · change c^2 * chargeBasisExpectation N
        (ChargeWord.comp (canonicalKleinSAdj h (2*h) x) (canonicalKleinS h (2*h) y)) = _
      rw [canonical_charge_selection_S_contract h (2*h) (by omega)]
      rfl
  have vertex_cauchy_coefficient {M h : ℕ} (hh : 0 < h)
      (hp : Bosonize.Ch18.HyperbolicPair) (N : Charge)
      (x y : Position (2 * h)) (channel : Bool) (n : ℕ) :
      let c : ℂ := (((2 * h : ℕ) : ℂ))⁻¹
      let K := fun z => if channel then canonicalKleinS h (2 * h) z else canonicalKleinD h (2 * h) z
      jointSeriesFunctional hp N
        (vertexSeriesMul (vertexWeylAdj (M := M) hh hp x channel)
          (vertexWeyl (M := M) hh hp y channel)) n =
        ∑ k ∈ Finset.range (n + 1), jointCoeffFunctional (M := M) hp N
          (vertexCoeffMul (vertexCoeffAdjoint (ChargeWord.scale c (K x), oscillatorExp (M := M) hp x channel k))
            (ChargeWord.scale c (K y), oscillatorExp (M := M) hp y channel (n-k))) := by
    classical
    let c : ℂ := (((2 * h : ℕ) : ℂ))⁻¹
    let K := fun z => if channel then canonicalKleinS h (2 * h) z else canonicalKleinD h (2 * h) z
    let ev : Multiset (vertexCoeff M) →+ ℂ :=
      { toFun := fun s => (s.map (jointCoeffFunctional (M := M) hp N)).sum
        map_zero' := by simp
        map_add' := by intro a b; simp }
    have hv (z : Position (2*h)) (k : ℕ) : vertexWeyl (M := M) hh hp z channel k =
        {((ChargeWord.scale c (K z), oscillatorExp (M := M) hp z channel k) : vertexCoeff M)} := by rfl
    have ha (k : ℕ) : vertexWeylAdj (M := M) hh hp x channel k =
        {vertexCoeffAdjoint ((ChargeWord.scale c (K x), oscillatorExp (M := M) hp x channel k) : vertexCoeff M)} := by
      change Multiset.map vertexCoeffAdjoint (vertexWeyl (M := M) hh hp x channel k) = _
      exact (congrArg (fun s : Multiset (vertexCoeff M) => s.map vertexCoeffAdjoint) (hv x k)).trans
        (Multiset.map_singleton vertexCoeffAdjoint _)
    change ev (∑ k ∈ Finset.range (n+1),
      ((vertexWeylAdj (M := M) hh hp x channel) k).bind fun a =>
        ((vertexWeyl (M := M) hh hp y channel) (n-k)).map fun b => vertexCoeffMul a b) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hb (a b : vertexCoeff M) :
        ev (({a} : Multiset (vertexCoeff M)).bind fun v => ({b} : Multiset (vertexCoeff M)).map fun u => vertexCoeffMul v u) =
        jointCoeffFunctional hp N (vertexCoeffMul a b) := by
      rw [Multiset.singleton_bind, Multiset.map_singleton]
      change (({vertexCoeffMul a b} : Multiset (vertexCoeff M)).map (jointCoeffFunctional hp N)).sum = _
      rw [Multiset.map_singleton, Multiset.sum_singleton]
    let a : vertexCoeff M := (ChargeWord.scale c (K x), oscillatorExp (M := M) hp x channel k)
    let b : vertexCoeff M := (ChargeWord.scale c (K y), oscillatorExp (M := M) hp y channel (n-k))
    exact (congrArg (fun s : Multiset (vertexCoeff M) => ev (s.bind fun v =>
        (vertexWeyl (M := M) hh hp y channel (n-k)).map fun u => vertexCoeffMul v u)) (ha k)).trans
      ((congrArg (fun s : Multiset (vertexCoeff M) => ev (({vertexCoeffAdjoint a} : Multiset (vertexCoeff M)).bind
        fun v => s.map fun u => vertexCoeffMul v u)) (hv y (n-k))).trans (hb (vertexCoeffAdjoint a) b))
  funext n
  let c : ℂ := (((2*h : ℕ) : ℂ))⁻¹
  let K := fun z => if channel then canonicalKleinS h (2*h) z else canonicalKleinD h (2*h) z
  let phase := Bosonize.A01.integerCharacter (Bosonize.A01.canonicalRoot (2*h))
    (if channel then aS N else aD N) ((y.val : ℤ) - (x.val : ℤ))
  have hterm (k : ℕ) : jointCoeffFunctional (M := M) hp N
      (vertexCoeffMul (vertexCoeffAdjoint (ChargeWord.scale c (K x), oscillatorExp (M := M) hp x channel k))
        (ChargeWord.scale c (K y), oscillatorExp (M := M) hp y channel (n-k))) =
      (c^2 * phase) * Bosonize.A08.omegaP M hp (oscSyntaxEval
        (oscSyntaxDagger (oscillatorExp (M := M) hp x channel k) * oscillatorExp (M := M) hp y channel (n-k))) := by
    rw [jointCoeffFunctional_product_contract]
    change chargeBasisExpectation N (ChargeWord.comp (ChargeWord.adjoint (ChargeWord.scale c (K x)))
      (ChargeWord.scale c (K y))) * _ = _
    exact congrArg (fun z : ℂ => z * Bosonize.A08.omegaP M hp (oscSyntaxEval
      (oscSyntaxDagger (oscillatorExp (M := M) hp x channel k) * oscillatorExp (M := M) hp y channel (n-k))))
      (vertex_charge_coefficient hh N x y channel)
  calc
    _ = ∑ k ∈ Finset.range (n+1), jointCoeffFunctional (M := M) hp N
        (vertexCoeffMul (vertexCoeffAdjoint (ChargeWord.scale c (K x), oscillatorExp (M := M) hp x channel k))
          (ChargeWord.scale c (K y), oscillatorExp (M := M) hp y channel (n-k))) :=
      vertex_cauchy_coefficient hh hp N x y channel n
    _ = ∑ k ∈ Finset.range (n+1), (c^2 * phase) * Bosonize.A08.omegaP M hp (oscSyntaxEval
        (oscSyntaxDagger (oscillatorExp (M := M) hp x channel k) * oscillatorExp (M := M) hp y channel (n-k))) := by
      apply Finset.sum_congr rfl
      intro k _
      exact hterm k
    _ = (c^2 * phase) * (∑ k ∈ Finset.range (n+1), Bosonize.A08.omegaP M hp (oscSyntaxEval
        (oscSyntaxDagger (oscillatorExp (M := M) hp x channel k) * oscillatorExp (M := M) hp y channel (n-k)))) := by
      rw [Finset.mul_sum]
    _ = (c^2 * phase) * ((Complex.I^n / (n.factorial : ℂ)) * Bosonize.A08.omegaP M hp
        ((Bosonize.V1S1.linearElement (if channel then xSForm hp y - xSForm hp x
          else xDForm hp y - xDForm hp x))^n)) :=
      congrArg (fun z : ℂ => (c^2 * phase) * z) (oscillator_cauchy_moment (M := M) hh hp x y channel n)
    _ = (c^2 * phase) * (if n % 2 = 0 then
        (-2 * (if channel then (gainS hp : ℂ) else (gainD hp : ℂ)) *
          (dirichletCutoff (2*h) M x y : ℂ))^(n/2) / ((n/2).factorial : ℂ) else 0) :=
      congrArg (fun z : ℂ => (c^2 * phase) * z) (gaussian_coefficient (M := M) hh hp x y channel n)
    _ = _ := by
      by_cases hn : n % 2 = 0 <;> simp [expectedWeylCorrelator, c, phase, hn]

theorem dressed_normal_prefactor_contract {M h : ℕ} (hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (N : Charge) (x y : Position (2 * h))
    (channel : Bool) :
    jointSeriesFunctional (M := M) hp N
      (vertexSeriesMul (M := M)
        (vertexSeriesScalarMul (dressedNormalMultiplier (M := M) hp channel)
          (vertexWeylAdj (M := M) hh hp x channel))
        (vertexWeylDressedNormal hh hp y channel)) =
      dressedNormalCorrelator (M := M) hh hp N x y channel := by
  classical
  have coefficient_scale {M : ℕ} (hp : Bosonize.Ch18.HyperbolicPair) (N : Charge) :
      ∀ (z w : ℂ) (a b : vertexCoeff M),
        jointCoeffFunctional hp N (vertexCoeffMul
          ((ChargeWord.scale z a.1, a.2) : vertexCoeff M)
          ((ChargeWord.scale w b.1, b.2) : vertexCoeff M)) =
        z*w*jointCoeffFunctional hp N (vertexCoeffMul a b) := by
    intro z w a b
    let S (r : ℂ) (c : vertexCoeff M) : vertexCoeff M := (ChargeWord.scale r c.1, c.2)
    change jointCoeffFunctional hp N (vertexCoeffMul (S z a) (S w b)) = _
    calc
      _ = chargeBasisExpectation N (vertexCoeffMul (S z a) (S w b)).1 *
        Bosonize.A08.omegaP M hp (oscSyntaxEval (vertexCoeffMul (S z a) (S w b)).2) :=
        jointCoeffFunctional_product_contract hp N _
      _ = z*w*(chargeBasisExpectation N (vertexCoeffMul a b).1 *
        Bosonize.A08.omegaP M hp (oscSyntaxEval (vertexCoeffMul a b).2)) := by
        dsimp [S, vertexCoeffMul, chargeBasisExpectation, ChargeWord.scale, ChargeWord.comp]
        split_ifs <;> simp_all
        ring
      _ = _ := congrArg (fun q : ℂ => z*w*q) (jointCoeffFunctional_product_contract hp N _).symm

  have multiset_scale_generic {A : Type} (F : A → ℂ) (P : A → A → A)
      (S : ℂ → A → A)
      (hc : ∀ z w a b, F (P (S z a) (S w b)) = z*w*F (P a b))
      (z w : ℂ) (u v : Multiset A) :
      (((u.map (S z)).bind fun a => (v.map (S w)).map fun b => P a b).map F).sum =
        z*w*(((u.bind fun a => v.map fun b => P a b).map F).sum) := by
    induction u using Multiset.induction with
    | empty => simp
    | cons a u ihu =>
      simp only [Multiset.map_cons, Multiset.cons_bind, Multiset.map_add, Multiset.sum_add, ihu]
      have hv : (((v.map (S w)).map (fun b => P (S z a) b)).map F).sum =
          z*w*((v.map (fun b => P a b)).map F).sum := by
        clear ihu
        induction v using Multiset.induction with
        | empty => simp
        | cons b v ihv =>
          simp only [Multiset.map_cons, Multiset.sum_cons, hc, ihv]
          ring
      rw [hv]
      ring
  have scalar_cauchy_shuffle (n : ℕ) (s t : ℕ → ℂ) (B : ℕ → ℕ → ℂ) :
      (∑ k ∈ Finset.range (n+1), ∑ i ∈ Finset.range (k+1), ∑ j ∈ Finset.range (n-k+1),
        s i * t j * B (k-i) (n-k-j)) =
      ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (a+1), ∑ i ∈ Finset.range (n-a+1),
        B b (a-b) * s i * t (n-a-i) := by
    classical
    let T : Finset (Σ _ : ℕ, ℕ × ℕ) := (Finset.range (n+1)).sigma
      (fun k => (Finset.range (k+1)).product (Finset.range (n-k+1)))
    calc
      _ = ∑ x ∈ T, s x.2.1 * t x.2.2 * B (x.1-x.2.1) (n-x.1-x.2.2) := by
        simp only [T, Finset.sum_sigma]
        apply Finset.sum_congr rfl
        intro k _
        exact (Finset.sum_product (Finset.range (k+1)) (Finset.range (n-k+1))
          (fun p : ℕ × ℕ => s p.1 * t p.2 * B (k-p.1) (n-k-p.2))).symm
      _ = ∑ x ∈ T, B x.2.1 (x.1-x.2.1) * s x.2.2 * t (n-x.1-x.2.2) := by
        apply Finset.sum_bij (fun x _ =>
          (⟨n - (x.2.1 + x.2.2), (x.1-x.2.1, x.2.1)⟩ : Σ _ : ℕ, ℕ × ℕ))
        · intro x hx
          rcases x with ⟨k, i, j⟩
          simp [T] at hx ⊢
          omega
        · intro x hx y hy heq
          rcases x with ⟨k, i, j⟩
          rcases y with ⟨l, p, q⟩
          simp [T] at hx hy
          have ha := congrArg (fun z : Σ _ : ℕ, ℕ × ℕ => z.1) heq
          have hb := congrArg (fun z : Σ _ : ℕ, ℕ × ℕ => z.2.1) heq
          have hc := congrArg (fun z : Σ _ : ℕ, ℕ × ℕ => z.2.2) heq
          have hkl : k = l := by dsimp at ha hb hc; omega
          have hip : i = p := by dsimp at hc; omega
          have hjq : j = q := by dsimp at ha; omega
          subst l
          subst p
          subst q
          rfl
        · intro y hy
          rcases y with ⟨a, b, i⟩
          simp [T] at hy
          let x : Σ _ : ℕ, ℕ × ℕ := ⟨b+i, (i,n-a-i)⟩
          refine ⟨x, ?_, ?_⟩
          · simp [x, T]
            omega
          · apply Sigma.ext
            · change n - (i + (n-a-i)) = a
              omega
            · apply heq_of_eq
              apply Prod.ext
              · change b+i-i = b
                omega
              · rfl
        · intro x hx
          rcases x with ⟨k, i, j⟩
          simp [T] at hx
          change s i * t j * B (k-i) (n-k-j) =
            B (k-i) (n-(i+j)-(k-i)) * s i * t (n-(n-(i+j))-i)
          rw [show n-(i+j)-(k-i) = n-k-j by omega,
            show n-(n-(i+j))-i = j by omega]
          ring
      _ = _ := by
        simp only [T, Finset.sum_sigma]
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_product (Finset.range (a+1)) (Finset.range (n-a+1))
          (fun p : ℕ × ℕ => B p.1 (a-p.1) * s p.2 * t (n-a-p.2))
  have bilinear_hom {A : Type} (F : A → ℂ) (P : A → A → A) :
      ∃ B : Multiset A →+ Multiset A →+ ℂ,
        ∀ u v, B u v = ((u.bind fun a => v.map fun b => P a b).map F).sum := by
    let E : Multiset A →+ ℂ :=
      { toFun := fun u => (u.map F).sum
        map_zero' := by simp
        map_add' := by intro u v; simp }
    let B : Multiset A →+ Multiset A →+ ℂ :=
      { toFun := fun u =>
          { toFun := fun v => E (u.bind fun a => v.map fun b => P a b)
            map_zero' := by simp
            map_add' := by intro v w; simp [Multiset.bind_add] }
        map_zero' := by ext v; simp
        map_add' := by intro u v; ext w; simp }
    exact ⟨B, fun _ _ => rfl⟩

  have generic_extract {A : Type} (F : A → ℂ) (P : A → A → A)
      (S : ℂ → A → A)
      (hc : ∀ z w a b, F (P (S z a) (S w b)) = z*w*F (P a b))
      (f g : ℕ → Multiset A) (s t : ℕ → ℂ) (n : ℕ) :
      (∑ k ∈ Finset.range (n+1),
        (((∑ i ∈ Finset.range (k+1), (f (k-i)).map (S (s i))).bind fun a =>
          (∑ j ∈ Finset.range (n-k+1), (g (n-k-j)).map (S (t j))).map
            (fun b => P a b)).map F).sum) =
      ∑ a ∈ Finset.range (n+1),
        (∑ b ∈ Finset.range (a+1), (((f b).bind fun x =>
          (g (a-b)).map (fun y => P x y)).map F).sum) *
        (∑ i ∈ Finset.range (n-a+1), s i*t (n-a-i)) := by
    classical
    obtain ⟨B, hB⟩ := bilinear_hom F P
    have hs (z w : ℂ) (u v : Multiset A) :
        B (u.map (S z)) (v.map (S w)) = z*w*B u v := by
      simpa only [hB] using multiset_scale_generic F P S hc z w u v
    calc
      _ = ∑ k ∈ Finset.range (n+1), ∑ i ∈ Finset.range (k+1),
          ∑ j ∈ Finset.range (n-k+1), s i*t j*B (f (k-i)) (g (n-k-j)) := by
        simp only [← hB, map_sum, AddMonoidHom.finsetSum_apply, hs]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
      _ = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (a+1),
          ∑ i ∈ Finset.range (n-a+1), B (f b) (g (a-b))*s i*t (n-a-i) :=
        scalar_cauchy_shuffle n s t (fun i j => B (f i) (g j))
      _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc, hB]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]

  have scalar_extract (f g : VertexSeries M) (s t : FormalSeries ℂ) :
      jointSeriesFunctional (M := M) hp N
        (vertexSeriesMul (vertexSeriesScalarMul s f) (vertexSeriesScalarMul t g)) =
      scalarSeriesMul (jointSeriesFunctional hp N (vertexSeriesMul f g))
        (scalarSeriesMul s t) := by
    apply funext
    intro n
    let E : Multiset (vertexCoeff M) →+ ℂ :=
      { toFun := fun u => (u.map (jointCoeffFunctional hp N)).sum
        map_zero' := by simp
        map_add' := by intro u v; simp }
    change E (∑ k ∈ Finset.range (n+1),
        ((∑ i ∈ Finset.range (k+1), (f (k-i)).map
          (fun a => ((ChargeWord.scale (s i) a.1,a.2) : vertexCoeff M))).bind fun a =>
          (∑ j ∈ Finset.range (n-k+1), (g (n-k-j)).map
            (fun b => ((ChargeWord.scale (t j) b.1,b.2) : vertexCoeff M))).map
              (fun b => vertexCoeffMul a b))) =
      ∑ a ∈ Finset.range (n+1),
        E (∑ b ∈ Finset.range (a+1), (f b).bind fun x =>
          (g (a-b)).map (fun y => vertexCoeffMul x y)) *
        (∑ i ∈ Finset.range (n-a+1), s i*t (n-a-i))
    simp only [map_sum]
    exact generic_extract (jointCoeffFunctional hp N) vertexCoeffMul
      (fun z a => ((ChargeWord.scale z a.1,a.2) : vertexCoeff M))
      (coefficient_scale hp N) f g s t n
  unfold vertexWeylDressedNormal dressedNormalCorrelator
  rw [scalar_extract, coefficientwise_weyl_correlator_contract]

theorem bare_normal_prefactor_contract {M h : ℕ} (hh : 0 < h)
    (hp : Bosonize.Ch18.HyperbolicPair) (N : Charge) (x y : Position (2 * h))
    (channel : Bool) :
    jointSeriesFunctional (M := M) hp N
      (vertexSeriesMul (M := M)
        (vertexSeriesScalarMul (bareNormalMultiplier M) (vertexWeylAdj (M := M) hh hp x channel))
        (vertexWeylBareNormal hh hp y channel)) =
      bareNormalCorrelator (M := M) hh hp N x y channel := by
  classical
  have coefficient_scale {M : ℕ} (hp : Bosonize.Ch18.HyperbolicPair) (N : Charge) :
      ∀ (z w : ℂ) (a b : vertexCoeff M),
        jointCoeffFunctional hp N (vertexCoeffMul
          ((ChargeWord.scale z a.1, a.2) : vertexCoeff M)
          ((ChargeWord.scale w b.1, b.2) : vertexCoeff M)) =
        z*w*jointCoeffFunctional hp N (vertexCoeffMul a b) := by
    intro z w a b
    let S (r : ℂ) (c : vertexCoeff M) : vertexCoeff M := (ChargeWord.scale r c.1, c.2)
    change jointCoeffFunctional hp N (vertexCoeffMul (S z a) (S w b)) = _
    calc
      _ = chargeBasisExpectation N (vertexCoeffMul (S z a) (S w b)).1 *
        Bosonize.A08.omegaP M hp (oscSyntaxEval (vertexCoeffMul (S z a) (S w b)).2) :=
        jointCoeffFunctional_product_contract hp N _
      _ = z*w*(chargeBasisExpectation N (vertexCoeffMul a b).1 *
        Bosonize.A08.omegaP M hp (oscSyntaxEval (vertexCoeffMul a b).2)) := by
        dsimp [S, vertexCoeffMul, chargeBasisExpectation, ChargeWord.scale, ChargeWord.comp]
        split_ifs <;> simp_all
        ring
      _ = _ := congrArg (fun q : ℂ => z*w*q) (jointCoeffFunctional_product_contract hp N _).symm

  have multiset_scale_generic {A : Type} (F : A → ℂ) (P : A → A → A)
      (S : ℂ → A → A)
      (hc : ∀ z w a b, F (P (S z a) (S w b)) = z*w*F (P a b))
      (z w : ℂ) (u v : Multiset A) :
      (((u.map (S z)).bind fun a => (v.map (S w)).map fun b => P a b).map F).sum =
        z*w*(((u.bind fun a => v.map fun b => P a b).map F).sum) := by
    induction u using Multiset.induction with
    | empty => simp
    | cons a u ihu =>
      simp only [Multiset.map_cons, Multiset.cons_bind, Multiset.map_add, Multiset.sum_add, ihu]
      have hv : (((v.map (S w)).map (fun b => P (S z a) b)).map F).sum =
          z*w*((v.map (fun b => P a b)).map F).sum := by
        clear ihu
        induction v using Multiset.induction with
        | empty => simp
        | cons b v ihv =>
          simp only [Multiset.map_cons, Multiset.sum_cons, hc, ihv]
          ring
      rw [hv]
      ring
  have scalar_cauchy_shuffle (n : ℕ) (s t : ℕ → ℂ) (B : ℕ → ℕ → ℂ) :
      (∑ k ∈ Finset.range (n+1), ∑ i ∈ Finset.range (k+1), ∑ j ∈ Finset.range (n-k+1),
        s i * t j * B (k-i) (n-k-j)) =
      ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (a+1), ∑ i ∈ Finset.range (n-a+1),
        B b (a-b) * s i * t (n-a-i) := by
    classical
    let T : Finset (Σ _ : ℕ, ℕ × ℕ) := (Finset.range (n+1)).sigma
      (fun k => (Finset.range (k+1)).product (Finset.range (n-k+1)))
    calc
      _ = ∑ x ∈ T, s x.2.1 * t x.2.2 * B (x.1-x.2.1) (n-x.1-x.2.2) := by
        simp only [T, Finset.sum_sigma]
        apply Finset.sum_congr rfl
        intro k _
        exact (Finset.sum_product (Finset.range (k+1)) (Finset.range (n-k+1))
          (fun p : ℕ × ℕ => s p.1 * t p.2 * B (k-p.1) (n-k-p.2))).symm
      _ = ∑ x ∈ T, B x.2.1 (x.1-x.2.1) * s x.2.2 * t (n-x.1-x.2.2) := by
        apply Finset.sum_bij (fun x _ =>
          (⟨n - (x.2.1 + x.2.2), (x.1-x.2.1, x.2.1)⟩ : Σ _ : ℕ, ℕ × ℕ))
        · intro x hx
          rcases x with ⟨k, i, j⟩
          simp [T] at hx ⊢
          omega
        · intro x hx y hy heq
          rcases x with ⟨k, i, j⟩
          rcases y with ⟨l, p, q⟩
          simp [T] at hx hy
          have ha := congrArg (fun z : Σ _ : ℕ, ℕ × ℕ => z.1) heq
          have hb := congrArg (fun z : Σ _ : ℕ, ℕ × ℕ => z.2.1) heq
          have hc := congrArg (fun z : Σ _ : ℕ, ℕ × ℕ => z.2.2) heq
          have hkl : k = l := by dsimp at ha hb hc; omega
          have hip : i = p := by dsimp at hc; omega
          have hjq : j = q := by dsimp at ha; omega
          subst l
          subst p
          subst q
          rfl
        · intro y hy
          rcases y with ⟨a, b, i⟩
          simp [T] at hy
          let x : Σ _ : ℕ, ℕ × ℕ := ⟨b+i, (i,n-a-i)⟩
          refine ⟨x, ?_, ?_⟩
          · simp [x, T]
            omega
          · apply Sigma.ext
            · change n - (i + (n-a-i)) = a
              omega
            · apply heq_of_eq
              apply Prod.ext
              · change b+i-i = b
                omega
              · rfl
        · intro x hx
          rcases x with ⟨k, i, j⟩
          simp [T] at hx
          change s i * t j * B (k-i) (n-k-j) =
            B (k-i) (n-(i+j)-(k-i)) * s i * t (n-(n-(i+j))-i)
          rw [show n-(i+j)-(k-i) = n-k-j by omega,
            show n-(n-(i+j))-i = j by omega]
          ring
      _ = _ := by
        simp only [T, Finset.sum_sigma]
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_product (Finset.range (a+1)) (Finset.range (n-a+1))
          (fun p : ℕ × ℕ => B p.1 (a-p.1) * s p.2 * t (n-a-p.2))
  have bilinear_hom {A : Type} (F : A → ℂ) (P : A → A → A) :
      ∃ B : Multiset A →+ Multiset A →+ ℂ,
        ∀ u v, B u v = ((u.bind fun a => v.map fun b => P a b).map F).sum := by
    let E : Multiset A →+ ℂ :=
      { toFun := fun u => (u.map F).sum
        map_zero' := by simp
        map_add' := by intro u v; simp }
    let B : Multiset A →+ Multiset A →+ ℂ :=
      { toFun := fun u =>
          { toFun := fun v => E (u.bind fun a => v.map fun b => P a b)
            map_zero' := by simp
            map_add' := by intro v w; simp [Multiset.bind_add] }
        map_zero' := by ext v; simp
        map_add' := by intro u v; ext w; simp }
    exact ⟨B, fun _ _ => rfl⟩

  have generic_extract {A : Type} (F : A → ℂ) (P : A → A → A)
      (S : ℂ → A → A)
      (hc : ∀ z w a b, F (P (S z a) (S w b)) = z*w*F (P a b))
      (f g : ℕ → Multiset A) (s t : ℕ → ℂ) (n : ℕ) :
      (∑ k ∈ Finset.range (n+1),
        (((∑ i ∈ Finset.range (k+1), (f (k-i)).map (S (s i))).bind fun a =>
          (∑ j ∈ Finset.range (n-k+1), (g (n-k-j)).map (S (t j))).map
            (fun b => P a b)).map F).sum) =
      ∑ a ∈ Finset.range (n+1),
        (∑ b ∈ Finset.range (a+1), (((f b).bind fun x =>
          (g (a-b)).map (fun y => P x y)).map F).sum) *
        (∑ i ∈ Finset.range (n-a+1), s i*t (n-a-i)) := by
    classical
    obtain ⟨B, hB⟩ := bilinear_hom F P
    have hs (z w : ℂ) (u v : Multiset A) :
        B (u.map (S z)) (v.map (S w)) = z*w*B u v := by
      simpa only [hB] using multiset_scale_generic F P S hc z w u v
    calc
      _ = ∑ k ∈ Finset.range (n+1), ∑ i ∈ Finset.range (k+1),
          ∑ j ∈ Finset.range (n-k+1), s i*t j*B (f (k-i)) (g (n-k-j)) := by
        simp only [← hB, map_sum, AddMonoidHom.finsetSum_apply, hs]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
      _ = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (a+1),
          ∑ i ∈ Finset.range (n-a+1), B (f b) (g (a-b))*s i*t (n-a-i) :=
        scalar_cauchy_shuffle n s t (fun i j => B (f i) (g j))
      _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc, hB]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]

  have scalar_extract (f g : VertexSeries M) (s t : FormalSeries ℂ) :
      jointSeriesFunctional (M := M) hp N
        (vertexSeriesMul (vertexSeriesScalarMul s f) (vertexSeriesScalarMul t g)) =
      scalarSeriesMul (jointSeriesFunctional hp N (vertexSeriesMul f g))
        (scalarSeriesMul s t) := by
    apply funext
    intro n
    let E : Multiset (vertexCoeff M) →+ ℂ :=
      { toFun := fun u => (u.map (jointCoeffFunctional hp N)).sum
        map_zero' := by simp
        map_add' := by intro u v; simp }
    change E (∑ k ∈ Finset.range (n+1),
        ((∑ i ∈ Finset.range (k+1), (f (k-i)).map
          (fun a => ((ChargeWord.scale (s i) a.1,a.2) : vertexCoeff M))).bind fun a =>
          (∑ j ∈ Finset.range (n-k+1), (g (n-k-j)).map
            (fun b => ((ChargeWord.scale (t j) b.1,b.2) : vertexCoeff M))).map
              (fun b => vertexCoeffMul a b))) =
      ∑ a ∈ Finset.range (n+1),
        E (∑ b ∈ Finset.range (a+1), (f b).bind fun x =>
          (g (a-b)).map (fun y => vertexCoeffMul x y)) *
        (∑ i ∈ Finset.range (n-a+1), s i*t (n-a-i))
    simp only [map_sum]
    exact generic_extract (jointCoeffFunctional hp N) vertexCoeffMul
      (fun z a => ((ChargeWord.scale z a.1,a.2) : vertexCoeff M))
      (coefficient_scale hp N) f g s t n
  unfold vertexWeylBareNormal bareNormalCorrelator
  rw [scalar_extract, coefficientwise_weyl_correlator_contract]

end Bosonize.V1S2
