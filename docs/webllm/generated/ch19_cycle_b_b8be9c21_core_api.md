# CH19 Core API closure (frozen Core; proofs omitted)

Only the Core declarations referenced by the task (transitively) are shown; definitions are complete, theorem headers omit proofs. Everything else in Core still exists. If you need a declaration that is not listed, say so instead of guessing its name.


## Bosonize/Core/A01FourierCharacters.lean

```lean
def integerCharacter (ζ : K) (k x : ℤ) : K := ζ ^ (k * x)

noncomputable def canonicalRoot (L : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (L : ℂ))

lemma root_ne_zero (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) : ζ ≠ 0 := …

lemma residue_character_int_cast (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) : residueCharacter L ζ (k : Ch01.Lattice L) (x : Ch01.Lattice L) = integerCharacter ζ k x := …

lemma character_sum (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Lattice L) : (∑ x : Ch01.Lattice L, residueCharacter L ζ k x) = if k = 0 then (L : K) else 0 := …

lemma canonical_root_primitive (L : ℕ) [NeZero L] : IsPrimitiveRoot (canonicalRoot L) L := …
```


## Bosonize/Core/A02CARHilbert.lean

```lean
abbrev Occupation (ι : Type*) := Finset ι

abbrev FockSpace (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  EuclideanSpace ℂ (Occupation ι)

noncomputable def occupationBasis (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Module.Basis (Occupation ι) ℂ (FockSpace ι) :=
  (occupationONB ι).toBasis

noncomputable def ket {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Occupation ι) : FockSpace ι := occupationBasis ι S

noncomputable def extendBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (images : Occupation ι → FockSpace ι) : Module.End ℂ (FockSpace ι) :=
  (occupationBasis ι).constr ℂ images

def commutator (A B : Module.End ℂ V) : Module.End ℂ V := A * B - B * A

lemma ket_norm (S : Occupation ι) : ‖ket S‖ = 1 := …

lemma ket_ne_zero (S : Occupation ι) : ket S ≠ 0 := …

lemma extend_basis_ket (images : Occupation ι → FockSpace ι) (S : Occupation ι) : extendBasis images (ket S) = images S := …
```


## Bosonize/Core/A03EnergyBudgets.lean

```lean
abbrev Operators (ι : Type*) [Fintype ι] [DecidableEq ι] := Module.End ℂ (A02.FockSpace ι)

noncomputable def diagonal (a : A02.Occupation ι → ℂ) : Operators ι :=
  A02.extendBasis (fun S => a S • A02.ket S)
```


## Bosonize/Core/A05MultiSpecies.lean

```lean
abbrev Mode (σ : Type*) (h : ℕ) := σ × Ch01.Band (2*h)

abbrev Occupation (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := A02.Occupation (Mode σ h)

abbrev FockSpace (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := A02.FockSpace (Mode σ h)

abbrev Operators (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := Module.End ℂ (FockSpace σ h)

def admissible (h : ℕ) (Ns : σ → ℤ) : Prop := ∀ ν, Ch07.admissible h (Ns ν)

noncomputable def jointConfiguration (h : ℕ) (Ss : σ → Ch07.Occupation h) : Occupation σ h :=
  Finset.univ.biUnion (fun ν => (Ss ν).image (fun k => (ν,k)))

noncomputable def groundConfiguration (h : ℕ) (Ns : σ → ℤ) : Occupation σ h :=
  jointConfiguration h (fun ν => Ch07.groundConfiguration h (Ns ν))

noncomputable def groundKet (h : ℕ) (Ns : σ → ℤ) : FockSpace σ h :=
  A02.ket (groundConfiguration h Ns)

noncomputable def annihilation (h : ℕ) (ν : σ) (k : Ch01.Band (2*h)) : Operators σ h :=
  Ch04.annihilation (ν,k)

noncomputable def creation (h : ℕ) (ν : σ) (k : Ch01.Band (2*h)) : Operators σ h :=
  Ch04.creation (ν,k)

noncomputable def rho (h : ℕ) (ν : σ) (m : ℤ) : Operators σ h :=
  ∑ z ∈ A04.validPairs (2*h) m, Ch04.hopping (ν,z.1) (ν,z.2)

lemma annihilation_car (h : ℕ) (i j : Mode σ h) : A02.anticommutator (annihilation h i.1 i.2) (annihilation h j.1 j.2) = 0 := …

lemma creation_car (h : ℕ) (i j : Mode σ h) : A02.anticommutator (creation h i.1 i.2) (creation h j.1 j.2) = 0 := …

lemma mixed_car (h : ℕ) (i j : Mode σ h) : A02.anticommutator (annihilation h i.1 i.2) (creation h j.1 j.2) = (if i=j then (1 : ℂ) else 0) • (1 : Operators σ h) := …

lemma rho_cross_commute (h : ℕ) (ν η : σ) (hne : ν ≠ η) (m n : ℤ) : A02.commutator (rho h ν m) (rho h η n) = 0 := …

lemma rho_lowering_budget_zero (h : ℕ) (hh : 0 < h) (ν : σ) (m K : ℕ) (hm : K < m) (Ns : σ → ℤ) (v : FockSpace σ h) (hv : v ∈ jointBudget h Ns K) : rho h ν (-(m : ℤ)) v = 0 := …

lemma ground_mem_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : admissible h Ns) (K : ℕ) : groundKet h Ns ∈ jointBudget h Ns K := …

lemma ground_ne_zero (h : ℕ) (Ns : σ → ℤ) : groundKet h Ns ≠ 0 := …
```


## Bosonize/Core/A06ChiralFields.lean

```lean
inductive Orientation where
  | right
  | left
  deriving DecidableEq

structure Branches (σ : Type*) where
  rightSpecies : σ
  leftSpecies : σ
  distinct : rightSpecies ≠ leftSpecies

def speciesOf {σ : Type*} (branches : Branches σ) : Orientation → σ
  | .right => branches.rightSpecies
  | .left => branches.leftSpecies

def marginAt (h M K : ℕ) (Ns : σ → ℤ) (ν : σ) : Prop :=
  2 * (M : ℤ) + (K : ℤ) + |Ns ν| ≤ (h : ℤ)

def branchMargins (h M K : ℕ) (Ns : σ → ℤ)
    (branches : Branches σ) : Prop :=
  marginAt h M K Ns branches.rightSpecies ∧
    marginAt h M K Ns branches.leftSpecies

noncomputable def latticeCharacter (h : ℕ) (ζ : ℂ) (k : ℤ)
    (x : ZMod (2 * h)) : ℂ :=
  A01.integerCharacter ζ k (x.val : ℤ)

lemma joint_signed_current_commutator (h K : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (m n : ℤ) (hmargin : |m| + |n| + (K : ℤ) + |Ns ν| ≤ (h : ℤ)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (A05.rho h ν m) (A05.rho h ν n) v = Ch10.schwingerCoefficient m n • v := …

lemma chiral_same_commutator_on_budget (h M K : ℕ) (hh : 0 < h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : Branches σ) (η : Orientation) (Ns : σ → ℤ) (hmargin : marginAt h M K Ns (speciesOf branches η)) (x y : ZMod (2 * h)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (chiralField h M ζ branches η x) (chiralField h M ζ branches η y) v = ((orientationSign η : ℂ) * skewKernel h M ζ x y) • v := …
```


## Bosonize/Core/A07InteractionsAndBogoliubov.lean

```lean
def oppositeOrientation : A06.Orientation → A06.Orientation
  | .right => .left
  | .left => .right

structure HyperbolicParams (v1 v2 : ℝ) where
  u : ℝ
  c : ℝ
  s : ℝ
  u_pos : 0 < u
  c_pos : 0 < c
  u_sq : u ^ 2 = v1 ^ 2 - v2 ^ 2
  hyperbolic_id : c ^ 2 - s ^ 2 = 1
  match_v1 : v1 = u * (c ^ 2 + s ^ 2)
  match_v2 : v2 = 2 * u * c * s

noncomputable def bogoliubovCreator (h m : ℕ) (c s : ℝ)
    (branches : A06.Branches σ) (η : A06.Orientation) :
    A05.Operators σ h :=
  (c : ℂ) • A05.rho h (A06.speciesOf branches η) (m : ℤ) +
    (s : ℂ) • A05.rho h (A06.speciesOf branches (oppositeOrientation η)) (-(m : ℤ))

noncomputable def bogoliubovAnnihilator (h m : ℕ) (c s : ℝ)
    (branches : A06.Branches σ) (η : A06.Orientation) :
    A05.Operators σ h :=
  (c : ℂ) • A05.rho h (A06.speciesOf branches η) (-(m : ℤ)) +
    (s : ℂ) • A05.rho h (A06.speciesOf branches (oppositeOrientation η)) (m : ℤ)

lemma pairing_mode_ground_nonzero (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (branches : A06.Branches σ) (hmargin : A06.branchMargins h M m Ns branches) : (A05.rho h branches.rightSpecies (m : ℤ) * A05.rho h branches.leftSpecies (m : ℤ) + A05.rho h branches.rightSpecies (-(m : ℤ)) * A05.rho h branches.leftSpecies (-(m : ℤ))) (A05.groundKet h Ns) ≠ 0 := …

lemma bogoliubov_creator_adjoint (h m : ℕ) (c s : ℝ) (branches : A06.Branches σ) (η : A06.Orientation) : LinearMap.adjoint (bogoliubovCreator h m c s branches η) = bogoliubovAnnihilator h m c s branches η := …

theorem bogoliubov_ccr_on_budget (h M K m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (bogoliubovAnnihilator h m c s branches η) (bogoliubovCreator h m c s branches η) v = (m : ℂ) • v := …
```


## Bosonize/Core/Ch05Fermions.lean

```lean
abbrev FockSpace (L : ℕ) := A02.FockSpace (Ch01.Band L)

abbrev Operators (L : ℕ) := Module.End ℂ (FockSpace L)

noncomputable def positionAnnihilation (L : ℕ) [NeZero L]
    (x : Ch01.Lattice L) : Operators L :=
  (A01.normalization L : ℂ) • ∑ k : Ch01.Band L,
    A01.bandCharacter L (A01.canonicalRoot L) k x • momentumAnnihilation L k

noncomputable def positionCreation (L : ℕ) [NeZero L]
    (x : Ch01.Lattice L) : Operators L :=
  (A01.normalization L : ℂ) • ∑ k : Ch01.Band L,
    A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) • momentumCreation L k

lemma position_creation_eq_adjoint (x : Ch01.Lattice L) : positionCreation L x = LinearMap.adjoint (positionAnnihilation L x) := …

lemma position_annihilation_car (x y : Ch01.Lattice L) : A02.anticommutator (positionAnnihilation L x) (positionAnnihilation L y) = 0 := …

lemma position_creation_car (x y : Ch01.Lattice L) : A02.anticommutator (positionCreation L x) (positionCreation L y) = 0 := …

lemma position_mixed_car (x y : Ch01.Lattice L) : A02.anticommutator (positionAnnihilation L x) (positionCreation L y) = (if x = y then (1 : ℂ) else 0) • (1 : Operators L) := …

lemma position_car_exists : ∃ R : A02.CAR (Ch01.Lattice L) (FockSpace L), R.annihilation = positionAnnihilation L ∧ R.creation = positionCreation L := …

lemma inverse_annihilation (k : Ch01.Band L) : momentumAnnihilation L k = (A01.normalization L : ℂ) • ∑ x : Ch01.Lattice L, A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) • positionAnnihilation L x := …
```


## Bosonize/Core/Ch06LocalNet.lean

```lean
abbrev FockSpace (L : ℕ) := Ch05.FockSpace L

abbrev Operators (L : ℕ) := Ch05.Operators L

abbrev Occupation (L : ℕ) := A02.Occupation (Ch01.Band L)
```


## Bosonize/Core/Ch07VacuumBudget.lean

```lean
abbrev Occupation (h : ℕ) := A02.Occupation (Ch01.Band (2*h))

abbrev FockSpace (h : ℕ) := Ch05.FockSpace (2*h)

abbrev Operators (h : ℕ) := Module.End ℂ (FockSpace h)

def admissible (h : ℕ) (N : ℤ) : Prop := -(h : ℤ) ≤ N ∧ N ≤ (h : ℤ)

def groundConfiguration (h : ℕ) (N : ℤ) : Occupation h :=
  Finset.univ.filter (fun k => k.val ≤ N)

noncomputable def groundKet (h : ℕ) (N : ℤ) (_hN : admissible h N) : FockSpace h :=
  A02.ket (groundConfiguration h N)
```


## Bosonize/Core/Ch08Boson.lean

```lean
abbrev Mode (M : ℕ) := Fin M

abbrev Exponents (M : ℕ) := Mode M →₀ ℕ

abbrev Polynomial (M : ℕ) := MvPolynomial (Mode M) ℂ

abbrev Operators (M : ℕ) := Module.End ℂ (Polynomial M)

def weight (M : ℕ) (i : Mode M) : ℕ :=
  i.val + 1

noncomputable def monomial (M : ℕ) (r : Exponents M) : Polynomial M :=
  MvPolynomial.monomial r 1

def monomialNorm (M : ℕ) (r : Exponents M) : ℕ :=
  ∏ i : Mode M, weight M i ^ r i * (r i).factorial

noncomputable def creation (M : ℕ) (i : Mode M) : Operators M :=
  LinearMap.mulLeft ℂ (MvPolynomial.X i)

noncomputable def derivative (M : ℕ) (i : Mode M) : Operators M :=
  (MvPolynomial.pderiv i).toLinearMap

noncomputable def annihilation (M : ℕ) (i : Mode M) : Operators M :=
  (weight M i : ℂ) • derivative M i

noncomputable def pairing (M : ℕ) (p q : Polynomial M) : ℂ :=
  ∑ r ∈ p.support, star (MvPolynomial.lcoeff ℂ r p) * (monomialNorm M r : ℂ) * MvPolynomial.lcoeff ℂ r q

noncomputable def commutator (M : ℕ) (A B : Operators M) : Operators M :=
  A * B - B * A

theorem creation_monomial (M : ℕ) (i : Mode M) (r : Exponents M) : creation M i (monomial M r) = monomial M (r + Finsupp.single i 1) := …

theorem derivative_monomial (M : ℕ) (i : Mode M) (r : Exponents M) : derivative M i (monomial M r) = (r i : ℂ) • monomial M (r - Finsupp.single i 1) := …

theorem annihilation_monomial (M : ℕ) (i : Mode M) (r : Exponents M) : annihilation M i (monomial M r) = ((weight M i * r i : ℕ) : ℂ) • monomial M (r - Finsupp.single i 1) := …

theorem pairing_monomials (M : ℕ) (r s : Exponents M) : pairing M (monomial M r) (monomial M s) = if r = s then (monomialNorm M r : ℂ) else 0 := …

theorem pairing_add_left (M : ℕ) (p q r : Polynomial M) : pairing M (p + q) r = pairing M p r + pairing M q r := …

theorem pairing_smul_left (M : ℕ) (a : ℂ) (p q : Polynomial M) : pairing M (a • p) q = star a * pairing M p q := …

theorem pairing_add_right (M : ℕ) (p q r : Polynomial M) : pairing M p (q + r) = pairing M p q + pairing M p r := …

theorem pairing_smul_right (M : ℕ) (a : ℂ) (p q : Polynomial M) : pairing M p (a • q) = a * pairing M p q := …

theorem creation_pairing_adjoint (M : ℕ) (i : Mode M) (p q : Polynomial M) : pairing M (creation M i p) q = pairing M p (annihilation M i q) := …

theorem ccr (M : ℕ) (i j : Mode M) : commutator M (annihilation M i) (creation M j) = if i = j then (weight M i : ℂ) • (1 : Operators M) else 0 := …

theorem creation_budget (M K : ℕ) (i : Mode M) (p : Polynomial M) (h : p ∈ budget M K) : creation M i p ∈ budget M (K + weight M i) := …

theorem annihilation_budget (M K : ℕ) (i : Mode M) (p : Polynomial M) (h : p ∈ budget M K) : annihilation M i p ∈ budget M (K - weight M i) := …

theorem annihilation_below_weight (M K : ℕ) (i : Mode M) (hK : K < weight M i) (p : Polynomial M) (hp : p ∈ budget M K) : annihilation M i p = 0 := …

theorem finite_ccr_obstruction (M K : ℕ) (i : Mode M) : finiteOperator M K (annihilation M i) * finiteOperator M K (creation M i) - finiteOperator M K (creation M i) * finiteOperator M K (annihilation M i) ≠ (weight M i : ℂ) • (1 : Module.End ℂ (FiniteFock M K)) := …

theorem formal_bch (M : ℕ) (i j : Mode M) (α β : ℂ) (n : ℕ) : formalProduct M (expCoefficient M (α • annihilation M i)) (expCoefficient M (β • creation M j)) n = formalProduct M (formalProduct M (expCoefficient M (β • creation M j)) (expCoefficient M (α • annihilation M i))) (gaussianCoefficient M (if i = j then (weight M i : ℂ) * α * β else 0)) n := …
```


## Bosonize/Core/Ch09DensityModes.lean

```lean
abbrev FockSpace (h : ℕ) := Ch07.FockSpace h

abbrev Operators (h : ℕ) := Module.End ℂ (FockSpace h)

noncomputable def rho (h : ℕ) (m : ℤ) : Operators h :=
  A04.dGamma (A04.shift (2*h) m)

lemma rho_lowering_budget_zero (h : ℕ) (hh : 0 < h) (m N K : ℤ) (hKm : K-m < 0) : ∀ v ∈ Ch07.fixedBudget h N K, rho h (-m) v = 0 := …
```


## Bosonize/Core/Ch12Sugawara.lean

```lean
abbrev FockSpace (h : ℕ) := Ch07.FockSpace h

abbrev Operators (h : ℕ) := Ch07.Operators h
```


## Bosonize/Core/Ch13KleinFactors.lean

```lean
abbrev FockSpace (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := A05.FockSpace σ h

abbrev Operators (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := A05.Operators σ h

lemma ground_field_coefficient (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (ν : σ) (hν : -(h : ℤ)+1 ≤ Ns ν) (b : σ → Ch06Ext.BoundaryTwist (2*h)) (x : ℤ) : inner ℂ (A05.groundKet h (lowerCharge Ns ν)) (A05.liftedAnnihilation h b ν x (A05.groundKet h Ns)) = (A01.normalization (2*h) : ℂ) * kleinPhase h Ns ν * Ch06Ext.liftPhase (2*h) (b ν) x * A01.canonicalRoot (2*h)^(x*Ns ν) := …
```


## Bosonize/Core/Ch16FieldHamiltonian.lean

```lean
noncomputable def excitedKet (h : ℕ) (Ns : σ → ℤ)
    (branches : A06.Branches σ) (η : A06.Orientation)
    (m : ℕ) : A05.FockSpace σ h :=
  A05.rho h (A06.speciesOf branches η) (m : ℤ) (A05.groundKet h Ns)

def standardBranches : A06.Branches (Fin 2) :=
  ⟨0, 1, by decide⟩

lemma chiral_spatial_collapse_on_budget (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hmargin : A06.marginAt h M K Ns (A06.speciesOf branches η)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : (∑ x : ZMod (2 * h), chiralSquare h M ζ branches η x) v = ((2 : ℂ) • (∑ m ∈ Finset.Icc 1 M, epsilon h ζ m • (A05.rho h (A06.speciesOf branches η) (m : ℤ) * A05.rho h (A06.speciesOf branches η) (-(m : ℤ))))) v := …

lemma excited_ket_mem_budget (h K m : ℕ) (hh : 0 < h) (hm : m ≤ K) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (branches : A06.Branches σ) (η : A06.Orientation) : excitedKet h Ns branches η m ∈ A05.jointBudget h Ns K := …

lemma excited_ket_nonzero (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (branches : A06.Branches σ) (η : A06.Orientation) (hmargin : A06.marginAt h M m Ns (A06.speciesOf branches η)) : excitedKet h Ns branches η m ≠ 0 := …

theorem single_mode_error_eigenvector (h M K m : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (hm : 1 ≤ m) (hcut : m ≤ M) (hK : m ≤ K) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hmargin : A06.branchMargins h M K Ns branches) : errorOperator h M ζ branches (excitedKet h Ns branches η m) = ((4 : ℂ) * (m : ℂ) * (epsilon h ζ m - referenceWeight h ζ)) • excitedKet h Ns branches η m := …

theorem first_mode_error_zero (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hK : 1 ≤ K) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hmargin : A06.branchMargins h M K Ns branches) : errorOperator h M ζ branches (excitedKet h Ns branches η 1) = 0 := …

theorem error_nonzero_witness (h M K m : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (hm : 1 ≤ m) (hcut : m ≤ M) (hK : m ≤ K) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (hweight : epsilon h ζ m ≠ referenceWeight h ζ) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hmargin : A06.branchMargins h M K Ns branches) : excitedKet h Ns branches η m ≠ 0 ∧ errorOperator h M ζ branches (excitedKet h Ns branches η m) ≠ 0 := …

theorem concrete_dispersion_gap : epsilon 8 (A01.canonicalRoot 16) 2 ≠ referenceWeight 8 (A01.canonicalRoot 16) := …

theorem concrete_excited_error_witness : A05.admissible 8 (fun _ : Fin 2 => 0) ∧ A06.branchMargins 8 2 2 (fun _ : Fin 2 => 0) standardBranches ∧ excitedKet 8 (fun _ : Fin 2 => 0) standardBranches .right 2 ≠ 0 ∧ errorOperator 8 2 (A01.canonicalRoot 16) standardBranches (excitedKet 8 (fun _ : Fin 2 => 0) standardBranches .right 2) ≠ 0 := …
```


## Bosonize/Core/Ch18Bogoliubov.lean

```lean
structure HyperbolicPair where
  c : ℝ
  s : ℝ
  hyperbolic_id : c ^ 2 - s ^ 2 = 1

def HyperbolicPair.ofParams {v1 v2 : ℝ}
    (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) : HyperbolicPair where
  c := hp.c
  s := hp.s
  hyperbolic_id := hp.hyperbolic_id

def luttingerG (hp : HyperbolicPair) : ℝ :=
  (hp.c - hp.s) ^ 2

def concreteV1 : ℝ := 17

def concreteV2 : ℝ := 15

def concreteNs : Fin 2 → ℤ := fun _ => 0

def concreteBranches : Bosonize.A06.Branches (Fin 2) :=
  Bosonize.Ch16.standardBranches

noncomputable def concreteParams : Bosonize.A07Interactions.HyperbolicParams concreteV1 concreteV2 where
  u := 8
  c := 5 / 4
  s := 3 / 4
  u_pos := by
    norm_num
  c_pos := by
    norm_num
  u_sq := by
    norm_num [concreteV1, concreteV2]
  hyperbolic_id := by
    norm_num
  match_v1 := by
    norm_num [concreteV1]
  match_v2 := by
    norm_num [concreteV2]

noncomputable def concretePair : HyperbolicPair :=
  HyperbolicPair.ofParams concreteParams

theorem luttingerG_mul_u_of_params {v1 v2 : ℝ} (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) : luttingerG (HyperbolicPair.ofParams hp) * hp.u = v1 - v2 := …

theorem luttingerG_eq_sqrt_of_params {v1 v2 : ℝ} (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) : luttingerG (HyperbolicPair.ofParams hp) = Real.sqrt ((v1 - v2) / (v1 + v2)) := …

theorem luttingerG_pos_of_params {v1 v2 : ℝ} (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) : 0 < luttingerG (HyperbolicPair.ofParams hp) := …

theorem concrete_velocity_match : concreteV1 = Bosonize.Ch17.v1Velocity concreteVF concreteG4 ∧ concreteV2 = Bosonize.Ch17.v2Velocity concreteG2 := …

theorem concreteParams_s_ne_zero : concreteParams.s ≠ 0 := …

theorem bogoliubov_creator_inverse_right (h m : ℕ) (hp : HyperbolicPair) (branches : Bosonize.A06.Branches σ) : Bosonize.A05.rho h branches.rightSpecies (m : ℤ) = (hp.c : ℂ) • Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches .right - (hp.s : ℂ) • Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .left := …

theorem bogoliubov_creator_inverse_left (h m : ℕ) (hp : HyperbolicPair) (branches : Bosonize.A06.Branches σ) : Bosonize.A05.rho h branches.leftSpecies (m : ℤ) = (hp.c : ℂ) • Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches .left - (hp.s : ℂ) • Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .right := …

theorem bogoliubov_annihilator_inverse_right (h m : ℕ) (hp : HyperbolicPair) (branches : Bosonize.A06.Branches σ) : Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) = (hp.c : ℂ) • Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .right - (hp.s : ℂ) • Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches .left := …

theorem bogoliubov_annihilator_inverse_left (h m : ℕ) (hp : HyperbolicPair) (branches : Bosonize.A06.Branches σ) : Bosonize.A05.rho h branches.leftSpecies (-(m : ℤ)) = (hp.c : ℂ) • Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .left - (hp.s : ℂ) • Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches .right := …

theorem bogoliubov_cross_annihilator_creator (h m : ℕ) (c s : ℝ) (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) : Bosonize.A02.commutator (Bosonize.A07Interactions.bogoliubovAnnihilator h m c s branches η) (Bosonize.A07Interactions.bogoliubovCreator h m c s branches (Bosonize.A07Interactions.oppositeOrientation η)) = 0 := …

theorem bogoliubov_cross_creator_creator_on_budget (h M K m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (c s : ℝ) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ) (hmargin : Bosonize.A06.branchMargins h M K Ns branches) (v : Bosonize.A05.FockSpace σ h) (hv : v ∈ Bosonize.A05.jointBudget h Ns K) : Bosonize.A02.commutator (Bosonize.A07Interactions.bogoliubovCreator h m c s branches .right) (Bosonize.A07Interactions.bogoliubovCreator h m c s branches .left) v = 0 := …

theorem bogoliubov_cross_annihilator_annihilator_on_budget (h M K m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (c s : ℝ) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ) (hmargin : Bosonize.A06.branchMargins h M K Ns branches) (v : Bosonize.A05.FockSpace σ h) (hv : v ∈ Bosonize.A05.jointBudget h Ns K) : Bosonize.A02.commutator (Bosonize.A07Interactions.bogoliubovAnnihilator h m c s branches .right) (Bosonize.A07Interactions.bogoliubovAnnihilator h m c s branches .left) v = 0 := …

theorem luttinger_hamiltonian_dressed_on_budget (h M K : ℕ) (hh : 0 < h) (vF g4 g2 mu : ℝ) {v1 v2 : ℝ} (hv1 : v1 = Bosonize.Ch17.v1Velocity vF g4) (hv2 : v2 = Bosonize.Ch17.v2Velocity g2) (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ) (hN : Bosonize.A05.admissible h Ns) (hSug : Bosonize.Ch17.sugawaraMargin h M K Ns branches) (hmargin : Bosonize.A06.branchMargins h M K Ns branches) (v : Bosonize.A05.FockSpace σ h) (hv : v ∈ Bosonize.A05.jointBudget h Ns K) : Bosonize.Ch17.luttingerFermionChosenModel h M vF g4 g2 mu branches v = (dressedOscillatorOp h M hp.u hp.c hp.s branches) v + (((Bosonize.Ch17.zeroModeEnergyScalar h vF g4 g2 mu branches Ns - vacuumShiftScalar h M hp.u hp.s : ℝ) : ℂ)) • v := …

theorem dressed_annihilator_ground_right (h m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) {v1 v2 : ℝ} (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ) (hN : Bosonize.A05.admissible h Ns) : Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .right (Bosonize.A05.groundKet h Ns) = (hp.s : ℂ) • Bosonize.Ch16.excitedKet h Ns branches .left m := …

theorem dressed_annihilator_ground_left (h m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) {v1 v2 : ℝ} (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ) (hN : Bosonize.A05.admissible h Ns) : Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .left (Bosonize.A05.groundKet h Ns) = (hp.s : ℂ) • Bosonize.Ch16.excitedKet h Ns branches .right m := …

theorem dressed_annihilator_ground_right_ne_zero (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) {v1 v2 : ℝ} (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) (hs : hp.s ≠ 0) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ) (hN : Bosonize.A05.admissible h Ns) (hmargin : Bosonize.A06.marginAt h M m Ns (Bosonize.A06.speciesOf branches .left)) : Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .right (Bosonize.A05.groundKet h Ns) ≠ 0 := …

theorem dressed_annihilator_ground_left_ne_zero (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) {v1 v2 : ℝ} (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) (hs : hp.s ≠ 0) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ) (hN : Bosonize.A05.admissible h Ns) (hmargin : Bosonize.A06.marginAt h M m Ns (Bosonize.A06.speciesOf branches .right)) : Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .left (Bosonize.A05.groundKet h Ns) ≠ 0 := …

theorem no_common_bare_dressed_vacuum (h M K m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) {v1 v2 : ℝ} (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) (hs : hp.s ≠ 0) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ) (hmargin : Bosonize.A06.branchMargins h M K Ns branches) (ψ : Bosonize.A05.FockSpace σ h) (hψ : ψ ≠ 0) (hψbudget : ψ ∈ Bosonize.A05.jointBudget h Ns K) (hbareR : Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) ψ = 0) (hbareL : Bosonize.A05.rho h branches.leftSpecies (-(m : ℤ)) ψ = 0) (hdressR : Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .right ψ = 0) (hdressL : Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .left ψ = 0) : False := …

theorem concrete_bogoliubov_witness : Bosonize.A05.admissible concreteCarrierH concreteNs ∧ Bosonize.A06.branchMargins concreteCarrierH concreteCutoff concreteBudget concreteNs concreteBranches ∧ Bosonize.Ch17.sugawaraMargin concreteCarrierH concreteCutoff concreteBudget concreteNs concreteBranches ∧ concreteParams.s ≠ 0 ∧ Bosonize.A05.groundKet concreteCarrierH concreteNs ∈ Bosonize.A05.jointBudget concreteCarrierH concreteNs concreteBudget ∧ Bosonize.A05.groundKet concreteCarrierH concreteNs ≠ 0 ∧ Bosonize.A07Interactions.bogoliubovAnnihilator concreteCarrierH concreteMode concreteParams.c concreteParams.s concreteBranches .right (Bosonize.A05.groundKet concreteCarrierH concreteNs) ≠ 0 ∧ Bosonize.A07Interactions.dressedModeNumber concreteCarrierH concreteMode concreteParams.u concreteParams.c concreteParams.s concreteBranches (Bosonize.A05.groundKet concreteCarrierH concreteNs) ≠ 0 ∧ vacuumShiftScalar concreteCarrierH concreteCutoff concreteParams.u concreteParams.s ≠ 0 ∧ vacuumShiftScalar concreteCarrierH concreteCutoff concreteParams.u concreteParams.s = 27 * Real.pi / 8 ∧ luttingerG concretePair = 1 / 4 ∧ 2 * concreteParams.u * concreteParams.s ^ 2 = 9 := …
```


## Bosonize/Core/A04DensityKinematics.lean

```lean
abbrev ShiftMatrix (L : ℕ) := Matrix (Ch01.Band L) (Ch01.Band L) ℂ

def validPairs (L : ℕ) (m : ℤ) : Finset (Ch01.Band L × Ch01.Band L) :=
  Finset.univ.filter (fun z => z.1.val = z.2.val + m)

def shift (L : ℕ) (m : ℤ) : ShiftMatrix L :=
  fun p k => if p.val = k.val + m then 1 else 0

noncomputable def dGamma {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) : Module.End ℂ (A02.FockSpace ι) :=
  ∑ p, ∑ k, A p k • Ch04.hopping p k
```


## Bosonize/Core/Ch01LatticeBand.lean

```lean
abbrev Lattice (L : ℕ) := ZMod L

def inBandPredicate (L : ℕ) (k : ℤ) : Prop := -(L : ℤ) < 2 * k ∧ 2 * k ≤ (L : ℤ)

abbrev Band (L : ℕ) := {k : ℤ // inBandPredicate L k}
```


## Bosonize/Core/Ch02UmbralCalculus.lean

```lean
def shift : Module.End R (S → R) where
  toFun f x := f (x + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
```


## Bosonize/Core/Ch04CARFock.lean

```lean
def fermionSign (i : ι) (S : A02.Occupation ι) : ℂ := (-1 : ℂ) ^ precedingCount i S

noncomputable def creation (i : ι) : Module.End ℂ (A02.FockSpace ι) :=
  A02.extendBasis fun S =>
    if i ∈ S then 0 else fermionSign i S • A02.ket (insert i S)

noncomputable def annihilation (i : ι) : Module.End ℂ (A02.FockSpace ι) :=
  A02.extendBasis fun S =>
    if i ∈ S then fermionSign i S • A02.ket (S.erase i) else 0

noncomputable def hopping (i j : ι) : Module.End ℂ (A02.FockSpace ι) :=
  creation i * annihilation j

lemma annihilation_car (i j : ι) : A02.anticommutator (annihilation i) (annihilation j) = 0 := …

lemma creation_car (i j : ι) : A02.anticommutator (creation i) (creation j) = 0 := …

lemma mixed_car (i j : ι) : A02.anticommutator (annihilation i) (creation j) = (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ (A02.FockSpace ι)) := …
```


## Bosonize/Core/Ch06Ext.lean

```lean
structure BoundaryTwist (L : ℕ) where
  step : ℂ
  norm_step : ‖step‖ = 1

noncomputable def liftPhase (L : ℕ) (b : BoundaryTwist L) (n : ℤ) : ℂ := b.step^n

noncomputable def annihilation (b : BoundaryTwist L) (n : ℤ) : Ch05.Operators L :=
  liftPhase L b n • Ch05.positionAnnihilation L (n : Ch01.Lattice L)

noncomputable def creation (b : BoundaryTwist L) (n : ℤ) : Ch05.Operators L :=
  star (liftPhase L b n) • Ch05.positionCreation L (n : Ch01.Lattice L)

lemma lifted_mixed_car (b : BoundaryTwist L) (n m : ℤ) : A02.anticommutator (annihilation L b n) (creation L b m) = (if (n : Ch01.Lattice L)=(m : Ch01.Lattice L) then liftPhase L b (n-m) else 0) • (1 : Ch05.Operators L) := …

omit [NeZero L] in lemma zero_mode_ket (b : BoundaryTwist L) (n referenceCharge : ℤ) (S : Ch06.Occupation L) : zeroMode L b n referenceCharge (A02.ket S) = (liftPhase L b n*A01.canonicalRoot L^(n*((S.card : ℤ)-referenceCharge))) • A02.ket S := …
```


## Bosonize/Core/Ch14Mandelstam.lean

```lean
lemma projected_map_apply (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ) (A : A05.Operators σ h) (v : A05.jointBudget h Ns Kin) : (projectedMap h Ns Nt Kin Kout A v : A05.FockSpace σ h) = projection h Nt Kout (A v) := …

lemma physical_occupation_expansion (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kout : ℕ) (S : A05.Occupation σ h) : projection h (Ch13.lowerCharge Ns ν) Kout (A05.liftedAnnihilation h b ν x (A02.ket S)) = (A01.normalization (2*h) : ℂ) • ∑ k : Ch01.Band (2*h), if (ν,k) ∈ S then (Ch06Ext.twistedCharacter (2*h) (b ν) k x * Ch04.fermionSign (ν,k) S) • projection h (Ch13.lowerCharge Ns ν) Kout (A02.ket (S.erase (ν,k))) else 0 := …

lemma physical_ground_expansion (h : ℕ) (hh : 0<h) (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (ν : σ) (x : ℤ) (Kin Kout : ℕ) : (physicalMap h b Ns ν x Kin Kout (groundVector h hh Ns hN Kin) : A05.FockSpace σ h) = (A01.normalization (2*h) : ℂ) • ∑ k : Ch01.Band (2*h), if (ν,k) ∈ A05.groundConfiguration h Ns then (Ch06Ext.twistedCharacter (2*h) (b ν) k x * Ch04.fermionSign (ν,k) (A05.groundConfiguration h Ns)) • projection h (Ch13.lowerCharge Ns ν) Kout (A02.ket ((A05.groundConfiguration h Ns).erase (ν,k))) else 0 := …
```


## Bosonize/Core/Ch17LuttingerModels.lean

```lean
theorem concrete_luttinger_witness : let Ns : Fin 2 → ℤ := fun _ => 0 A05.admissible 8 Ns ∧ A06.branchMargins 8 2 2 Ns Ch16.standardBranches ∧ sugawaraMargin 8 2 2 Ns Ch16.standardBranches ∧ A05.groundKet 8 Ns ∈ A05.jointBudget 8 Ns 2 ∧ A05.groundKet 8 Ns ≠ 0 ∧ luttingerBosonizedHamiltonian 8 2 1 (6 * Real.pi) (6 * Real.pi) (canonicalMu 8 1) Ch16.standardBranches (A05.groundKet 8 Ns) ≠ 0 := …
```


## Bosonize/Core/A07FiniteNormalOrdering.lean

```lean
lemma contraction_on_joint_budget (h M K : ℕ) (hh : 0 < h) (branches : A06.Branches σ) (Ns : σ → ℤ) (p q : Letter M) (hp : p.2.2 = false) (hq : q.2.2 = true) (hbranch : p.1 = q.1) (hmargin : A06.marginAt h M K Ns (A06.speciesOf branches (orientation p.1))) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : (normalPair h M branches p q - rawPair h M branches p q) v = (if natMode p = natMode q then -(natMode p : ℂ) else 0) • v := …
```


## Bosonize/Core/Ch15DualFields.lean

```lean
theorem zero_mode_obstruction_on_ground (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hmargin : A06.branchMargins h M K Ns branches) (x : ZMod (2 * h)) (c : ℂ) (hc : c ≠ 0) : ¬ (∀ y : ZMod (2 * h), A02.commutator (phiField h M ζ branches x) (A06.opForwardDiff h (thetaField h M ζ branches) y) (A05.groundKet h Ns) = (c * A06.dirichletKernel h M ζ x y) • A05.groundKet h Ns) := …
```
