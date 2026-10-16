# CH20 Core API closure (frozen Core; proofs omitted)

Only the Core declarations referenced by the task (transitively) are shown; definitions are complete, theorem headers omit proofs. Everything else in Core still exists. If you need a declaration that is not listed, say so instead of guessing its name.


## Bosonize/Core/A01FourierCharacters.lean

```lean
def integerCharacter (ζ : K) (k x : ℤ) : K := ζ ^ (k * x)

noncomputable def canonicalRoot (L : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (L : ℂ))

noncomputable def normalization (L : ℕ) : ℝ := (Real.sqrt (L : ℝ))⁻¹

lemma root_ne_zero (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) : ζ ≠ 0 := …

lemma residue_character_int_cast (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) : residueCharacter L ζ (k : Ch01.Lattice L) (x : Ch01.Lattice L) = integerCharacter ζ k x := …

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

lemma ket_inner (S T : Occupation ι) : inner ℂ (ket S) (ket T) = if S = T then (1 : ℂ) else 0 := …

lemma ket_norm (S : Occupation ι) : ‖ket S‖ = 1 := …

lemma ket_ne_zero (S : Occupation ι) : ket S ≠ 0 := …

lemma extend_basis_ket (images : Occupation ι → FockSpace ι) (S : Occupation ι) : extendBasis images (ket S) = images S := …
```


## Bosonize/Core/A03EnergyBudgets.lean

```lean
abbrev Operators (ι : Type*) [Fintype ι] [DecidableEq ι] := Module.End ℂ (A02.FockSpace ι)

noncomputable def coordinateSpace (U : Set (A02.Occupation ι)) : Submodule ℂ (A02.FockSpace ι) :=
  Submodule.span ℂ (A02.ket '' U)

noncomputable def diagonal (a : A02.Occupation ι → ℂ) : Operators ι :=
  A02.extendBasis (fun S => a S • A02.ket S)

noncomputable def coordinateProjection (U : Set (A02.Occupation ι)) : Operators ι := by
  classical
  exact diagonal (fun S => if S ∈ U then 1 else 0)

lemma ket_mem_coordinate_space (U : Set (A02.Occupation ι)) (S : A02.Occupation ι) : A02.ket S ∈ coordinateSpace U ↔ S ∈ U := …

lemma exact_shift_charge_commutator (charge energy : A02.Occupation ι → ℤ) (A : Operators ι) (q d : ℤ) (hA : ExactShift charge energy A q d) : A02.commutator (diagonal (fun S => (charge S : ℂ))) A = (q : ℂ) • A := …

lemma exact_shift_energy_commutator (charge energy : A02.Occupation ι → ℤ) (A : Operators ι) (q d : ℤ) (hA : ExactShift charge energy A q d) : A02.commutator (diagonal (fun S => (energy S : ℂ))) A = (d : ℂ) • A := …
```


## Bosonize/Core/A05MultiSpecies.lean

```lean
abbrev Mode (σ : Type*) (h : ℕ) := σ × Ch01.Band (2*h)

abbrev Occupation (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := A02.Occupation (Mode σ h)

abbrev FockSpace (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := A02.FockSpace (Mode σ h)

abbrev Operators (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := Module.End ℂ (FockSpace σ h)

noncomputable abbrev jointBudget (h : ℕ) (Ns : σ → ℤ) (K : ℕ) := Ch07.speciesBudget h Ns (K : ℤ)

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

noncomputable def chargeObservable (h : ℕ) (ν : σ) : Operators σ h :=
  A03.diagonal (fun S => (Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) : ℂ))

noncomputable def liftedAnnihilation (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (ν : σ) (x : ℤ) : Operators σ h :=
  (A01.normalization (2*h) : ℂ) •
    ∑ k : Ch01.Band (2*h), Ch06Ext.twistedCharacter (2*h) (b ν) k x • annihilation h ν k

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

def orientationSign : Orientation → ℤ
  | .right => 1
  | .left => -1

structure Branches (σ : Type*) where
  rightSpecies : σ
  leftSpecies : σ
  distinct : rightSpecies ≠ leftSpecies

def speciesOf {σ : Type*} (branches : Branches σ) : Orientation → σ
  | .right => branches.rightSpecies
  | .left => branches.leftSpecies

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

noncomputable def pairingMode (h m : ℕ) (v1 v2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  (v1 : ℂ) • (A05.rho h r (m : ℤ) * A05.rho h r (-(m : ℤ)) +
    A05.rho h l (m : ℤ) * A05.rho h l (-(m : ℤ))) +
  (v2 : ℂ) • (A05.rho h r (m : ℤ) * A05.rho h l (m : ℤ) +
    A05.rho h r (-(m : ℤ)) * A05.rho h l (-(m : ℤ)))

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

lemma bogoliubov_creator_adjoint (h m : ℕ) (c s : ℝ) (branches : A06.Branches σ) (η : A06.Orientation) : LinearMap.adjoint (bogoliubovCreator h m c s branches η) = bogoliubovAnnihilator h m c s branches η := …

theorem bogoliubov_expansion_on_budget (h M K m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (v1 v2 : ℝ) (hp : HyperbolicParams v1 v2) (branches : A06.Branches σ) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : dressedModeNumber h m hp.u hp.c hp.s branches v = pairingMode h m v1 v2 branches v + ((2 * hp.u * hp.s ^ 2 * (m : ℝ) : ℝ) : ℂ) • v := …

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

lemma inverse_annihilation (k : Ch01.Band L) : momentumAnnihilation L k = (A01.normalization L : ℂ) • ∑ x : Ch01.Lattice L, A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) • positionAnnihilation L x := …
```


## Bosonize/Core/Ch06Ext.lean

```lean
structure BoundaryTwist (L : ℕ) where
  step : ℂ
  norm_step : ‖step‖ = 1

def periodicTwist (L : ℕ) : BoundaryTwist L := ⟨1, norm_one⟩

noncomputable def liftPhase (L : ℕ) (b : BoundaryTwist L) (n : ℤ) : ℂ := b.step^n

noncomputable def annihilation (b : BoundaryTwist L) (n : ℤ) : Ch05.Operators L :=
  liftPhase L b n • Ch05.positionAnnihilation L (n : Ch01.Lattice L)

noncomputable def creation (b : BoundaryTwist L) (n : ℤ) : Ch05.Operators L :=
  star (liftPhase L b n) • Ch05.positionCreation L (n : Ch01.Lattice L)

noncomputable def twistedCharacter (b : BoundaryTwist L) (k : Ch01.Band L) (n : ℤ) : ℂ :=
  liftPhase L b n * A01.integerCharacter (A01.canonicalRoot L) k.val n

lemma twisted_fourier_inverse (b : BoundaryTwist L) (k : Ch01.Band L) : Ch05.momentumAnnihilation L k = (A01.normalization L : ℂ) • ∑ x : Ch01.Lattice L, star (twistedCharacter L b k (x.val : ℤ)) • siteAnnihilation L b x := …

lemma annihilation_fourier (b : BoundaryTwist L) (n : ℤ) : annihilation L b n = (A01.normalization L : ℂ) • ∑ k : Ch01.Band L, twistedCharacter L b k n • Ch05.momentumAnnihilation L k := …

lemma periodic_field (n : ℤ) : annihilation L (periodicTwist L) n = Ch05.positionAnnihilation L (n : Ch01.Lattice L) := …

lemma lifted_mixed_car (b : BoundaryTwist L) (n m : ℤ) : A02.anticommutator (annihilation L b n) (creation L b m) = (if (n : Ch01.Lattice L)=(m : Ch01.Lattice L) then liftPhase L b (n-m) else 0) • (1 : Ch05.Operators L) := …

omit [NeZero L] in lemma zero_mode_ket (b : BoundaryTwist L) (n referenceCharge : ℤ) (S : Ch06.Occupation L) : zeroMode L b n referenceCharge (A02.ket S) = (liftPhase L b n*A01.canonicalRoot L^(n*((S.card : ℤ)-referenceCharge))) • A02.ket S := …
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

def relativeCharge (h : ℕ) (S : Occupation h) : ℤ := (S.card : ℤ)-(h : ℤ)

def groundConfiguration (h : ℕ) (N : ℤ) : Occupation h :=
  Finset.univ.filter (fun k => k.val ≤ N)

noncomputable def groundKet (h : ℕ) (N : ℤ) (_hN : admissible h N) : FockSpace h :=
  A02.ket (groundConfiguration h N)

noncomputable def chargeObservable (h : ℕ) : Operators h :=
  A03.diagonal (fun S => (relativeCharge h S : ℂ))

def speciesConfiguration (h : ℕ) (S : A02.Occupation (σ × Ch01.Band (2*h))) (ν : σ) : Occupation h :=
  (S.filter (fun p => p.1 = ν)).image Prod.snd

def totalExcitation (h : ℕ) (S : A02.Occupation (σ × Ch01.Band (2*h))) : ℤ :=
  ∑ ν : σ, excitationEnergy h (speciesConfiguration h S ν)

noncomputable def speciesBudget (h : ℕ) (Ns : σ → ℤ) (K : ℤ) :
    Submodule ℂ (A02.FockSpace (σ × Ch01.Band (2*h))) :=
  A03.coordinateSpace {S | (∀ ν, relativeCharge h (speciesConfiguration h S ν) = Ns ν) ∧
    totalExcitation h S ≤ K}

lemma species_budget_ket (h : ℕ) (S : A02.Occupation (σ × Ch01.Band (2*h))) (Ns : σ → ℤ) (K : ℤ) : A02.ket S ∈ speciesBudget h Ns K ↔ (∀ ν, relativeCharge h (speciesConfiguration h S ν) = Ns ν) ∧ totalExcitation h S ≤ K := …
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

def energy (M : ℕ) (r : Exponents M) : ℕ :=
  ∑ i : Mode M, weight M i * r i

def monomialNorm (M : ℕ) (r : Exponents M) : ℕ :=
  ∏ i : Mode M, weight M i ^ r i * (r i).factorial

noncomputable def normalization (M : ℕ) (r : Exponents M) : ℂ :=
  (Real.sqrt (monomialNorm M r : ℝ) : ℂ)

noncomputable def creation (M : ℕ) (i : Mode M) : Operators M :=
  LinearMap.mulLeft ℂ (MvPolynomial.X i)

noncomputable def derivative (M : ℕ) (i : Mode M) : Operators M :=
  (MvPolynomial.pderiv i).toLinearMap

noncomputable def annihilation (M : ℕ) (i : Mode M) : Operators M :=
  (weight M i : ℂ) • derivative M i

noncomputable def commutator (M : ℕ) (A B : Operators M) : Operators M :=
  A * B - B * A

noncomputable def projection (M K : ℕ) : Operators M :=
  (MvPolynomial.basisMonomials (Mode M) ℂ).constr ℂ (fun r => if energy M r ≤ K then monomial M r else 0)

theorem creation_monomial (M : ℕ) (i : Mode M) (r : Exponents M) : creation M i (monomial M r) = monomial M (r + Finsupp.single i 1) := …

theorem derivative_monomial (M : ℕ) (i : Mode M) (r : Exponents M) : derivative M i (monomial M r) = (r i : ℂ) • monomial M (r - Finsupp.single i 1) := …

theorem annihilation_monomial (M : ℕ) (i : Mode M) (r : Exponents M) : annihilation M i (monomial M r) = ((weight M i * r i : ℕ) : ℂ) • monomial M (r - Finsupp.single i 1) := …

theorem pairing_monomials (M : ℕ) (r s : Exponents M) : pairing M (monomial M r) (monomial M s) = if r = s then (monomialNorm M r : ℂ) else 0 := …

theorem ccr (M : ℕ) (i j : Mode M) : commutator M (annihilation M i) (creation M j) = if i = j then (weight M i : ℂ) • (1 : Operators M) else 0 := …

theorem projection_monomial (M K : ℕ) (r : Exponents M) : projection M K (monomial M r) = if energy M r ≤ K then monomial M r else 0 := …
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

def lowerCharge (Ns : σ → ℤ) (ν : σ) : σ → ℤ := Function.update Ns ν (Ns ν-1)

def phaseExponent (h : ℕ) (Ns : σ → ℤ) (ν : σ) : ℤ :=
  (∑ η ∈ Finset.univ.filter (· < ν), ((h : ℤ)+Ns η)) + ((h : ℤ)+Ns ν-1)

noncomputable def kleinPhase (h : ℕ) (Ns : σ → ℤ) (ν : σ) : ℂ :=
  (-1 : ℂ) ^ phaseExponent h Ns ν

lemma ground_top_annihilation (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (ν : σ) (hν : -(h : ℤ)+1 ≤ Ns ν) (k : Ch01.Band (2*h)) (hk : k.val=Ns ν) : A05.annihilation h ν k (A05.groundKet h Ns) = kleinPhase h Ns ν • A05.groundKet h (lowerCharge Ns ν) := …

lemma ground_field_coefficient (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (ν : σ) (hν : -(h : ℤ)+1 ≤ Ns ν) (b : σ → Ch06Ext.BoundaryTwist (2*h)) (x : ℤ) : inner ℂ (A05.groundKet h (lowerCharge Ns ν)) (A05.liftedAnnihilation h b ν x (A05.groundKet h Ns)) = (A01.normalization (2*h) : ℂ) * kleinPhase h Ns ν * Ch06Ext.liftPhase (2*h) (b ν) x * A01.canonicalRoot (2*h)^(x*Ns ν) := …
```


## Bosonize/Core/Ch14Mandelstam.lean

```lean
def budgetSet (h : ℕ) (Ns : σ → ℤ) (K : ℕ) : Set (A05.Occupation σ h) :=
  {S | (∀ ν, Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) = Ns ν) ∧
    Ch07.totalExcitation h S ≤ (K : ℤ)}

noncomputable def projection (h : ℕ) (Ns : σ → ℤ) (K : ℕ) : A05.Operators σ h :=
  A03.coordinateProjection (budgetSet h Ns K)

noncomputable def projectedMap (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ)
    (A : A05.Operators σ h) : A05.jointBudget h Ns Kin →ₗ[ℂ] A05.jointBudget h Nt Kout :=
  (projection h Nt Kout * A).domRestrict (A05.jointBudget h Ns Kin) |>.codRestrict
    (A05.jointBudget h Nt Kout) (fun v => by
      change projection h Nt Kout (A v.val) ∈ A03.coordinateSpace (budgetSet h Nt Kout)
      rw [← A03.projection_range]
      exact ⟨A v.val, rfl⟩)

noncomputable def budgetAdjoint (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ)
    (A : A05.jointBudget h Ns Kin →ₗ[ℂ] A05.jointBudget h Nt Kout) :
    A05.jointBudget h Nt Kout →ₗ[ℂ] A05.jointBudget h Ns Kin :=
  LinearMap.adjoint (𝕜 := ℂ) (E := A05.jointBudget h Ns Kin) (F := A05.jointBudget h Nt Kout) A

noncomputable def groundVector (h : ℕ) (hh : 0<h) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (K : ℕ) : A05.jointBudget h Ns K :=
  ⟨A05.groundKet h Ns, A05.ground_mem_budget h hh Ns hN K⟩

lemma projected_map_apply (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ) (A : A05.Operators σ h) (v : A05.jointBudget h Ns Kin) : (projectedMap h Ns Nt Kin Kout A v : A05.FockSpace σ h) = projection h Nt Kout (A v) := …

lemma projected_map_adjoint (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ) (A : A05.Operators σ h) : budgetAdjoint h Ns Nt Kin Kout (projectedMap h Ns Nt Kin Kout A) = projectedMap h Nt Ns Kout Kin (LinearMap.adjoint A) := …

lemma vertex_candidate_adjoint (h M : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kin Kout : ℕ) : let Nt := Ch13.lowerCharge Ns ν budgetAdjoint h Ns Nt Kin Kout (vertexCandidate h M b Ns ν x Kin Kout) = (A01.normalization (2*h) : ℂ) • (budgetAdjoint h Ns Ns Kin Kin (zeroMode h b Ns ν x Kin)).comp ((budgetAdjoint h Ns Nt Kin Kin (projectedMap h Ns Nt Kin Kin (Ch13.kleinKernel h Ns ν Kin))).comp ((budgetAdjoint h Nt Nt Kin Kin (A05Exp.finiteTaylor Kin (projectedMap h Nt Nt Kin Kin (wPlus h M ν x)))).comp ((budgetAdjoint h Nt Nt Kin Kout (projectedMap h Nt Nt Kin Kout LinearMap.id)).comp (budgetAdjoint h Nt Nt Kout Kout (A05Exp.finiteTaylor Kout (projectedMap h Nt Nt Kout Kout (wMinus h M ν x))))))) := …

lemma physical_occupation_expansion (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kout : ℕ) (S : A05.Occupation σ h) : projection h (Ch13.lowerCharge Ns ν) Kout (A05.liftedAnnihilation h b ν x (A02.ket S)) = (A01.normalization (2*h) : ℂ) • ∑ k : Ch01.Band (2*h), if (ν,k) ∈ S then (Ch06Ext.twistedCharacter (2*h) (b ν) k x * Ch04.fermionSign (ν,k) S) • projection h (Ch13.lowerCharge Ns ν) Kout (A02.ket (S.erase (ν,k))) else 0 := …

lemma physical_ground_expansion (h : ℕ) (hh : 0<h) (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (ν : σ) (x : ℤ) (Kin Kout : ℕ) : (physicalMap h b Ns ν x Kin Kout (groundVector h hh Ns hN Kin) : A05.FockSpace σ h) = (A01.normalization (2*h) : ℂ) • ∑ k : Ch01.Band (2*h), if (ν,k) ∈ A05.groundConfiguration h Ns then (Ch06Ext.twistedCharacter (2*h) (b ν) k x * Ch04.fermionSign (ν,k) (A05.groundConfiguration h Ns)) • projection h (Ch13.lowerCharge Ns ν) Kout (A02.ket ((A05.groundConfiguration h Ns).erase (ν,k))) else 0 := …
```


## Bosonize/Core/Ch16FieldHamiltonian.lean

```lean
def standardBranches : A06.Branches (Fin 2) :=
  ⟨0, 1, by decide⟩

lemma chiral_spatial_collapse_on_budget (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hmargin : A06.marginAt h M K Ns (A06.speciesOf branches η)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : (∑ x : ZMod (2 * h), chiralSquare h M ζ branches η x) v = ((2 : ℂ) • (∑ m ∈ Finset.Icc 1 M, epsilon h ζ m • (A05.rho h (A06.speciesOf branches η) (m : ℤ) * A05.rho h (A06.speciesOf branches η) (-(m : ℤ))))) v := …
```


## Bosonize/Core/Ch17LuttingerModels.lean

```lean
noncomputable def v1Velocity (vF g4 : ℝ) : ℝ :=
  vF + g4 / (2 * Real.pi)

noncomputable def v2Velocity (g2 : ℝ) : ℝ :=
  g2 / (2 * Real.pi)

noncomputable def canonicalMu (h : ℕ) (vF : ℝ) : ℝ :=
  Real.pi * vF / ((2 * h : ℕ) : ℝ)

noncomputable def zeroModeEnergyScalar {σ : Type*} (h : ℕ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) : ℝ :=
  let L : ℝ := ((2 * h : ℕ) : ℝ)
  let nr : ℝ := (Ns branches.rightSpecies : ℝ)
  let nl : ℝ := (Ns branches.leftSpecies : ℝ)
  (2 * Real.pi * vF / L) * (nr * (nr + 1) / 2 + nl * (nl + 1) / 2) +
    (g4 / (2 * L)) * (nr ^ 2 + nl ^ 2) +
    (g2 / L) * nr * nl -
    mu * (nr + nl)

noncomputable def symmetricZeroModeScalar {σ : Type*} (h : ℕ)
    (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) : ℝ :=
  let L : ℝ := ((2 * h : ℕ) : ℝ)
  let nr : ℝ := (Ns branches.rightSpecies : ℝ)
  let nl : ℝ := (Ns branches.leftSpecies : ℝ)
  (Real.pi * v1Velocity vF g4 / L) * (nr ^ 2 + nl ^ 2) +
    (g2 / L) * nr * nl

lemma zero_mode_scalar_canonical_mu {σ : Type*} (h : ℕ) (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) : zeroModeEnergyScalar h vF g4 g2 (canonicalMu h vF) branches Ns = symmetricZeroModeScalar h vF g4 g2 branches Ns := …

lemma zero_mode_op_on_budget (h K : ℕ) (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : zeroModeEnergyOp h vF g4 g2 mu branches v = (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v := …

theorem luttinger_hamiltonian_on_budget (h M K : ℕ) (hh : 0 < h) (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hSug : sugawaraMargin h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : luttingerFermionChosenModel h M vF g4 g2 mu branches v = luttingerOscillatorOp h M vF g4 g2 branches v + (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v := …

theorem luttinger_hamiltonian_canonical_mu_on_budget (h M K : ℕ) (hh : 0 < h) (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hSug : sugawaraMargin h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : luttingerFermionChosenModel h M vF g4 g2 (canonicalMu h vF) branches v = luttingerOscillatorOp h M vF g4 g2 branches v + (symmetricZeroModeScalar h vF g4 g2 branches Ns : ℂ) • v := …

theorem luttinger_raw_intra_on_budget (h M K : ℕ) (hh : 0 < h) (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hSug : sugawaraMargin h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : (freeFermionKinetic h vF branches + A07Interactions.rawIntraBranch h M g4 branches + A07Interactions.pairingInterBranch h M g2 branches - chemicalPotentialOp h mu branches) v = luttingerOscillatorOp h M vF g4 g2 branches v + (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v - (((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) • (A07Interactions.seaWickCorrection h M branches.rightSpecies + A07Interactions.seaWickCorrection h M branches.leftSpecies)) v := …

theorem concrete_luttinger_witness : let Ns : Fin 2 → ℤ := fun _ => 0 A05.admissible 8 Ns ∧ A06.branchMargins 8 2 2 Ns Ch16.standardBranches ∧ sugawaraMargin 8 2 2 Ns Ch16.standardBranches ∧ A05.groundKet 8 Ns ∈ A05.jointBudget 8 Ns 2 ∧ A05.groundKet 8 Ns ≠ 0 ∧ luttingerBosonizedHamiltonian 8 2 1 (6 * Real.pi) (6 * Real.pi) (canonicalMu 8 1) Ch16.standardBranches (A05.groundKet 8 Ns) ≠ 0 := …
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

def luttingerGInv (hp : HyperbolicPair) : ℝ :=
  (hp.c + hp.s) ^ 2

def concreteV1 : ℝ := 17

def concreteV2 : ℝ := 15

def concreteNs : Fin 2 → ℤ := fun _ => 0

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

theorem luttingerGInv_mul_u_of_params {v1 v2 : ℝ} (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) : luttingerGInv (HyperbolicPair.ofParams hp) * hp.u = v1 + v2 := …

theorem luttingerGInv_pos_of_params {v1 v2 : ℝ} (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) : 0 < luttingerGInv (HyperbolicPair.ofParams hp) := …

theorem concrete_velocity_match : concreteV1 = Bosonize.Ch17.v1Velocity concreteVF concreteG4 ∧ concreteV2 = Bosonize.Ch17.v2Velocity concreteG2 := …

theorem concreteParams_s_ne_zero : concreteParams.s ≠ 0 := …

theorem bogoliubov_creator_inverse_right (h m : ℕ) (hp : HyperbolicPair) (branches : Bosonize.A06.Branches σ) : Bosonize.A05.rho h branches.rightSpecies (m : ℤ) = (hp.c : ℂ) • Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches .right - (hp.s : ℂ) • Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .left := …

theorem bogoliubov_creator_inverse_left (h m : ℕ) (hp : HyperbolicPair) (branches : Bosonize.A06.Branches σ) : Bosonize.A05.rho h branches.leftSpecies (m : ℤ) = (hp.c : ℂ) • Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches .left - (hp.s : ℂ) • Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .right := …

theorem bogoliubov_annihilator_inverse_right (h m : ℕ) (hp : HyperbolicPair) (branches : Bosonize.A06.Branches σ) : Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) = (hp.c : ℂ) • Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .right - (hp.s : ℂ) • Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches .left := …

theorem bogoliubov_annihilator_inverse_left (h m : ℕ) (hp : HyperbolicPair) (branches : Bosonize.A06.Branches σ) : Bosonize.A05.rho h branches.leftSpecies (-(m : ℤ)) = (hp.c : ℂ) • Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches .left - (hp.s : ℂ) • Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches .right := …

theorem bogoliubov_cross_annihilator_creator (h m : ℕ) (c s : ℝ) (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) : Bosonize.A02.commutator (Bosonize.A07Interactions.bogoliubovAnnihilator h m c s branches η) (Bosonize.A07Interactions.bogoliubovCreator h m c s branches (Bosonize.A07Interactions.oppositeOrientation η)) = 0 := …

theorem luttinger_oscillator_dressed_on_budget (h M K : ℕ) (hh : 0 < h) (vF g4 g2 : ℝ) {v1 v2 : ℝ} (hv1 : v1 = Bosonize.Ch17.v1Velocity vF g4) (hv2 : v2 = Bosonize.Ch17.v2Velocity g2) (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ) (hmargin : Bosonize.A06.branchMargins h M K Ns branches) (v : Bosonize.A05.FockSpace σ h) (hv : v ∈ Bosonize.A05.jointBudget h Ns K) : Bosonize.Ch17.luttingerOscillatorOp h M vF g4 g2 branches v = (dressedOscillatorOp h M hp.u hp.c hp.s branches) v - (((vacuumShiftScalar h M hp.u hp.s : ℝ) : ℂ)) • v := …

theorem luttinger_hamiltonian_dressed_on_budget (h M K : ℕ) (hh : 0 < h) (vF g4 g2 mu : ℝ) {v1 v2 : ℝ} (hv1 : v1 = Bosonize.Ch17.v1Velocity vF g4) (hv2 : v2 = Bosonize.Ch17.v2Velocity g2) (hp : Bosonize.A07Interactions.HyperbolicParams v1 v2) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ) (hN : Bosonize.A05.admissible h Ns) (hSug : Bosonize.Ch17.sugawaraMargin h M K Ns branches) (hmargin : Bosonize.A06.branchMargins h M K Ns branches) (v : Bosonize.A05.FockSpace σ h) (hv : v ∈ Bosonize.A05.jointBudget h Ns K) : Bosonize.Ch17.luttingerFermionChosenModel h M vF g4 g2 mu branches v = (dressedOscillatorOp h M hp.u hp.c hp.s branches) v + (((Bosonize.Ch17.zeroModeEnergyScalar h vF g4 g2 mu branches Ns - vacuumShiftScalar h M hp.u hp.s : ℝ) : ℂ)) • v := …

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

lemma annihilation_ket (i : ι) (S : A02.Occupation ι) : annihilation i (A02.ket S) = if i ∈ S then fermionSign i S • A02.ket (S.erase i) else 0 := …
```


## Bosonize/Core/Ch19Correlations.lean

```lean
theorem omegaP_creator_annihilator_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) : Bosonize.A08.omegaP M hp (Bosonize.A08.creatorGen M .right i * Bosonize.A08.annihilatorGen M .right j) = if i = j then ((i.val + 1 : ℕ) : ℂ) * (hp.s : ℂ) ^ 2 else 0 := …

theorem omegaP_annihilator_creator_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) : Bosonize.A08.omegaP M hp (Bosonize.A08.annihilatorGen M .right i * Bosonize.A08.creatorGen M .right j) = if i = j then ((i.val + 1 : ℕ) : ℂ) * (hp.c : ℂ) ^ 2 else 0 := …

theorem omegaP_cross_creator_creator (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) : Bosonize.A08.omegaP M hp (Bosonize.A08.creatorGen M .right i * Bosonize.A08.creatorGen M .left j) = if i = j then -(((i.val + 1 : ℕ) : ℂ) * (hp.c : ℂ) * (hp.s : ℂ)) else 0 := …

theorem ordered_density_kernel (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0) (hp : Bosonize.Ch18.HyperbolicPair) (x y : ZMod (2 * h)) : orderedDensityCorrelation h M ζ hp x y = densityKernel h M ζ (hp.c ^ 2) (hp.s ^ 2) ((x.val : ℤ) - (y.val : ℤ)) := …

theorem ground_lowering_raising (h M : ℕ) (hh : 0 < h) (m n : ℕ) (hm : 1 ≤ m) (hmM : m ≤ M) (hnM : n ≤ M) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ) (hN : Bosonize.A05.admissible h Ns) (hmargin : Bosonize.A06.marginAt h M 0 Ns branches.rightSpecies) : Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns) (Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) * Bosonize.A05.rho h branches.rightSpecies (n : ℤ)) = if m = n then (m : ℂ) else 0 := …

theorem ground_dressed_number (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hmM : m ≤ M) (hp : Bosonize.Ch18.HyperbolicPair) (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) (Ns : σ → ℤ) (hN : Bosonize.A05.admissible h Ns) (hmargin : Bosonize.A06.branchMargins h M 0 Ns branches) : Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns) (Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches η * Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches η) = (m : ℂ) * (hp.s : ℂ) ^ 2 := …

theorem ground_dressed_reverse (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hmM : m ≤ M) (hp : Bosonize.Ch18.HyperbolicPair) (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) (Ns : σ → ℤ) (hN : Bosonize.A05.admissible h Ns) (hmargin : Bosonize.A06.branchMargins h M 0 Ns branches) : Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns) (Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches η * Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches η) = (m : ℂ) * (hp.c : ℂ) ^ 2 := …

theorem ground_not_dressed_vacuum (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hmM : m ≤ M) (hp : Bosonize.Ch18.HyperbolicPair) (hs : hp.s ≠ 0) (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) (Ns : σ → ℤ) (hN : Bosonize.A05.admissible h Ns) (hmargin : Bosonize.A06.branchMargins h M 0 Ns branches) : Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns) (Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches η * Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches η) ≠ 0 := …

theorem fock_ground_density_kernel (h M : ℕ) [NeZero (2 * h)] (hh : 0 < h) (ζ : ℂ) (hζ : ζ ≠ 0) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ) (hN : Bosonize.A05.admissible h Ns) (hmargin : Bosonize.A06.marginAt h M 0 Ns branches.rightSpecies) (x y : ZMod (2 * h)) : Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns) (fockDensityR h M ζ branches x * fockDensityR h M ζ branches y) = densityKernel h M ζ 1 0 ((x.val : ℤ) - (y.val : ℤ)) := …

theorem concrete_correlation_witness : Bosonize.A08.omegaP 2 Bosonize.Ch18.concretePair (Bosonize.A08.creatorGen 2 .right (1 : Fin 2) * Bosonize.A08.annihilatorGen 2 .right (1 : Fin 2)) = (9 : ℂ) / 8 ∧ Bosonize.A08.omegaP 2 Bosonize.Ch18.concretePair (Bosonize.A08.annihilatorGen 2 .right (1 : Fin 2) * Bosonize.A08.creatorGen 2 .right (1 : Fin 2)) = (25 : ℂ) / 8 ∧ Bosonize.A08.omegaP 2 Bosonize.Ch18.concretePair (Bosonize.A08.creatorGen 2 .right (1 : Fin 2) * Bosonize.A08.creatorGen 2 .left (1 : Fin 2)) = -(15 : ℂ) / 8 ∧ orderedDensityCorrelation 8 2 (Bosonize.A01.canonicalRoot (2 * 8)) Bosonize.Ch18.concretePair 0 0 = (51 : ℂ) / 2048 ∧ Bosonize.A06.branchMargins 8 2 0 Bosonize.Ch18.concreteNs Bosonize.Ch18.concreteBranches ∧ Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs) (Bosonize.A05.rho 8 0 (-2) * Bosonize.A05.rho 8 0 2) = 2 ∧ Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs) (Bosonize.A07Interactions.bogoliubovCreator 8 2 Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s Bosonize.Ch18.concreteBranches .right * Bosonize.A07Interactions.bogoliubovAnnihilator 8 2 Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s Bosonize.Ch18.concreteBranches .right) = (9 : ℂ) / 8 ∧ Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs) (Bosonize.A07Interactions.bogoliubovCreator 8 2 Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s Bosonize.Ch18.concreteBranches .right * Bosonize.A07Interactions.bogoliubovAnnihilator 8 2 Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s Bosonize.Ch18.concreteBranches .right) ≠ 0 ∧ Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs) (fockDensityR 8 2 (Bosonize.A01.canonicalRoot (2 * 8)) Bosonize.Ch18.concreteBranches 0 * fockDensityR 8 2 (Bosonize.A01.canonicalRoot (2 * 8)) Bosonize.Ch18.concreteBranches 0) = (3 : ℂ) / 256 := …
```
