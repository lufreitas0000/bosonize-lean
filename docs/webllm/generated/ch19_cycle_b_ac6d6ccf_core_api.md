# CH19 Core API closure (frozen Core; proofs omitted)

Only the Core declarations referenced by the task (transitively) are shown; definitions are complete, theorem headers omit proofs. Everything else in Core still exists. If you need a declaration that is not listed, say so instead of guessing its name.


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

lemma ket_apply (S T : Occupation ι) : ket S T = if T = S then (1 : ℂ) else 0 := …

lemma coordinates_ket (S T : Occupation ι) : coordinates ι (ket S) T = if T = S then (1 : ℂ) else 0 := …

lemma occupation_expansion (v : FockSpace ι) : v = ∑ S : Occupation ι, v S • ket S := …

lemma extend_basis_ket (images : Occupation ι → FockSpace ι) (S : Occupation ι) : extendBasis images (ket S) = images S := …

lemma end_ext_basis (A B : Module.End ℂ (FockSpace ι)) (h : ∀ S : Occupation ι, A (ket S) = B (ket S)) : A = B := …

lemma adjoint_of_basis_pairing (A B : Module.End ℂ (FockSpace ι)) (h : ∀ S T : Occupation ι, inner ℂ (ket S) (A (ket T)) = inner ℂ (B (ket S)) (ket T)) : B = LinearMap.adjoint A := …
```


## Bosonize/Core/A03EnergyBudgets.lean

```lean
abbrev Operators (ι : Type*) [Fintype ι] [DecidableEq ι] := Module.End ℂ (A02.FockSpace ι)

noncomputable def diagonal (a : A02.Occupation ι → ℂ) : Operators ι :=
  A02.extendBasis (fun S => a S • A02.ket S)

lemma diagonal_ket (a : A02.Occupation ι → ℂ) (S : A02.Occupation ι) : diagonal a (A02.ket S) = a S • A02.ket S := …

lemma diagonal_adjoint (a : A02.Occupation ι → ℂ) : LinearMap.adjoint (diagonal a) = diagonal (fun S => star (a S)) := …

lemma coordinate_space_support (U : Set (A02.Occupation ι)) (v : A02.FockSpace ι) : v ∈ coordinateSpace U ↔ ∀ S, S ∉ U → A02.coordinates ι v S = 0 := …

lemma exact_shift_charge_commutator (charge energy : A02.Occupation ι → ℤ) (A : Operators ι) (q d : ℤ) (hA : ExactShift charge energy A q d) : A02.commutator (diagonal (fun S => (charge S : ℂ))) A = (q : ℂ) • A := …

lemma exact_shift_energy_commutator (charge energy : A02.Occupation ι → ℤ) (A : Operators ι) (q d : ℤ) (hA : ExactShift charge energy A q d) : A02.commutator (diagonal (fun S => (energy S : ℂ))) A = (d : ℂ) • A := …
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

lemma species_joint_configuration (h : ℕ) (Ss : σ → Ch07.Occupation h) (ν : σ) : Ch07.speciesConfiguration h (jointConfiguration h Ss) ν = Ss ν := …

lemma joint_species_configuration (h : ℕ) (S : Occupation σ h) : jointConfiguration h (fun ν => Ch07.speciesConfiguration h S ν) = S := …

lemma tensor_kets (h : ℕ) (Ss : σ → Ch07.Occupation h) : tensorVector h (fun ν => A02.ket (Ss ν)) = A02.ket (jointConfiguration h Ss) := …

lemma rho_cross_commute (h : ℕ) (ν η : σ) (hne : ν ≠ η) (m n : ℤ) : A02.commutator (rho h ν m) (rho h η n) = 0 := …
```


## Bosonize/Core/A06ChiralFields.lean

```lean
inductive Orientation where
  | right
  | left
  deriving DecidableEq

lemma joint_signed_current_commutator (h K : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (m n : ℤ) (hmargin : |m| + |n| + (K : ℤ) + |Ns ν| ≤ (h : ℤ)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (A05.rho h ν m) (A05.rho h ν n) v = Ch10.schwingerCoefficient m n • v := …

lemma chiral_same_commutator_on_budget (h M K : ℕ) (hh : 0 < h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : Branches σ) (η : Orientation) (Ns : σ → ℤ) (hmargin : marginAt h M K Ns (speciesOf branches η)) (x y : ZMod (2 * h)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (chiralField h M ζ branches η x) (chiralField h M ζ branches η y) v = ((orientationSign η : ℂ) * skewKernel h M ζ x y) • v := …
```


## Bosonize/Core/A07InteractionsAndBogoliubov.lean

```lean
def oppositeOrientation : A06.Orientation → A06.Orientation
  | .right => .left
  | .left => .right

theorem bogoliubov_ccr_on_budget (h M K m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (bogoliubovAnnihilator h m c s branches η) (bogoliubovCreator h m c s branches η) v = (m : ℂ) • v := …
```


## Bosonize/Core/Ch05Fermions.lean

```lean
abbrev FockSpace (L : ℕ) := A02.FockSpace (Ch01.Band L)

abbrev Operators (L : ℕ) := Module.End ℂ (FockSpace L)

lemma total_number_ket (S : A02.Occupation (Ch01.Band L)) : totalNumber L (A02.ket S) = (S.card : ℂ) • A02.ket S := …

lemma bare_hamiltonian_ket (S : A02.Occupation (Ch01.Band L)) : bareHamiltonian L (A02.ket S) = (occupationEnergy L S : ℂ) • A02.ket S := …

lemma shifted_hamiltonian_ket (S : A02.Occupation (Ch01.Band L)) : shiftedHamiltonian L (A02.ket S) = ((occupationEnergy L S - seaEnergy L : ℤ) : ℂ) • A02.ket S := …
```


## Bosonize/Core/Ch06LocalNet.lean

```lean
abbrev FockSpace (L : ℕ) := Ch05.FockSpace L

abbrev Operators (L : ℕ) := Ch05.Operators L

abbrev Occupation (L : ℕ) := A02.Occupation (Ch01.Band L)

omit [NeZero L] in lemma matrix_unit_expansion (A : Operators L) : A = ∑ S : Occupation L, ∑ T : Occupation L, (A (A02.ket T)) S • matrixUnit L S T := …
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

lemma ground_configuration_card (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) : ((groundConfiguration h N).card : ℤ) = (h : ℤ)+N := …

lemma ground_configuration_charge (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) : relativeCharge h (groundConfiguration h N) = N := …

lemma ground_configuration_energy (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) : relativeEnergy h (groundConfiguration h N) = groundEnergy N := …

lemma ground_configuration_excitation (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) : excitationEnergy h (groundConfiguration h N) = 0 := …

lemma excitation_zero_iff_ground (h : ℕ) (hh : 0 < h) (S : Occupation h) : excitationEnergy h S = 0 ↔ S = groundConfiguration h (relativeCharge h S) := …

lemma species_budget_ket (h : ℕ) (S : A02.Occupation (σ × Ch01.Band (2*h))) (Ns : σ → ℤ) (K : ℤ) : A02.ket S ∈ speciesBudget h Ns K ↔ (∀ ν, relativeCharge h (speciesConfiguration h S ν) = Ns ν) ∧ totalExcitation h S ≤ K := …
```


## Bosonize/Core/Ch08Boson.lean

```lean
abbrev Mode (M : ℕ) := Fin M

abbrev Exponents (M : ℕ) := Mode M →₀ ℕ

abbrev Polynomial (M : ℕ) := MvPolynomial (Mode M) ℂ

abbrev Operators (M : ℕ) := Module.End ℂ (Polynomial M)

noncomputable def monomial (M : ℕ) (r : Exponents M) : Polynomial M :=
  MvPolynomial.monomial r 1

noncomputable def commutator (M : ℕ) (A B : Operators M) : Operators M :=
  A * B - B * A

theorem creation_monomial (M : ℕ) (i : Mode M) (r : Exponents M) : creation M i (monomial M r) = monomial M (r + Finsupp.single i 1) := …

theorem derivative_monomial (M : ℕ) (i : Mode M) (r : Exponents M) : derivative M i (monomial M r) = (r i : ℂ) • monomial M (r - Finsupp.single i 1) := …

theorem annihilation_monomial (M : ℕ) (i : Mode M) (r : Exponents M) : annihilation M i (monomial M r) = ((weight M i * r i : ℕ) : ℂ) • monomial M (r - Finsupp.single i 1) := …

theorem number_monomial (M : ℕ) (r : Exponents M) : numberOperator M (monomial M r) = (particleCount M r : ℂ) • monomial M r := …

theorem hamiltonian_monomial (M : ℕ) (r : Exponents M) : hamiltonian M (monomial M r) = (energy M r : ℂ) • monomial M r := …

theorem pairing_monomials (M : ℕ) (r s : Exponents M) : pairing M (monomial M r) (monomial M s) = if r = s then (monomialNorm M r : ℂ) else 0 := …

theorem creation_pairing_adjoint (M : ℕ) (i : Mode M) (p q : Polynomial M) : pairing M (creation M i p) q = pairing M p (annihilation M i q) := …

theorem ccr (M : ℕ) (i j : Mode M) : commutator M (annihilation M i) (creation M j) = if i = j then (weight M i : ℂ) • (1 : Operators M) else 0 := …

theorem creation_budget (M K : ℕ) (i : Mode M) (p : Polynomial M) (h : p ∈ budget M K) : creation M i p ∈ budget M (K + weight M i) := …

theorem annihilation_budget (M K : ℕ) (i : Mode M) (p : Polynomial M) (h : p ∈ budget M K) : annihilation M i p ∈ budget M (K - weight M i) := …

theorem annihilation_below_weight (M K : ℕ) (i : Mode M) (hK : K < weight M i) (p : Polynomial M) (hp : p ∈ budget M K) : annihilation M i p = 0 := …

theorem annihilation_power_budget (M K : ℕ) (i : Mode M) (p : Polynomial M) (h : p ∈ budget M K) : (annihilation M i ^ (K + 1)) p = 0 := …

theorem projection_monomial (M K : ℕ) (r : Exponents M) : projection M K (monomial M r) = if energy M r ≤ K then monomial M r else 0 := …
```


## Bosonize/Core/Ch09DensityModes.lean

```lean
abbrev FockSpace (h : ℕ) := Ch07.FockSpace h

abbrev Operators (h : ℕ) := Module.End ℂ (FockSpace h)
```


## Bosonize/Core/Ch12Sugawara.lean

```lean
abbrev FockSpace (h : ℕ) := Ch07.FockSpace h

abbrev Operators (h : ℕ) := Ch07.Operators h

theorem sugawara_signed_commutator (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : Ch07.admissible h N) (K J M : ℕ) (n : ℤ) (hshift : (K : ℤ)+n ≤ (J : ℤ)) (hMK : K ≤ M) (hMJ : J ≤ M) (hsource : 2*(K : ℤ)+|N| ≤ (h : ℤ)) (htarget : 2*(J : ℤ)+|N| ≤ (h : ℤ)) (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) : A02.commutator (sugawaraHamiltonian h M) (Ch09.rho h n) v = (n : ℂ) • Ch09.rho h n v := …

theorem sugawara_raising_commutator (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : Ch07.admissible h N) (K M n : ℕ) (hM : K+n ≤ M) (hR2 : 2*((K+n : ℕ) : ℤ)+|N| ≤ (h : ℤ)) (v : FockSpace h) (hv : v ∈ Ch07.fixedBudget h N (K : ℤ)) : A02.commutator (sugawaraHamiltonian h M) (Ch09.rho h (n : ℤ)) v = (n : ℂ) • Ch09.rho h (n : ℤ) v := …
```


## Bosonize/Core/Ch13KleinFactors.lean

```lean
abbrev FockSpace (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := A05.FockSpace σ h

abbrev Operators (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := A05.Operators σ h

lemma ground_top_annihilation (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (ν : σ) (hν : -(h : ℤ)+1 ≤ Ns ν) (k : Ch01.Band (2*h)) (hk : k.val=Ns ν) : A05.annihilation h ν k (A05.groundKet h Ns) = kleinPhase h Ns ν • A05.groundKet h (lowerCharge Ns ν) := …
```


## Bosonize/Core/Ch18Bogoliubov.lean

```lean
structure HyperbolicPair where
  c : ℝ
  s : ℝ
  hyperbolic_id : c ^ 2 - s ^ 2 = 1

theorem bogoliubov_cross_annihilator_creator (h m : ℕ) (c s : ℝ) (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) : Bosonize.A02.commutator (Bosonize.A07Interactions.bogoliubovAnnihilator h m c s branches η) (Bosonize.A07Interactions.bogoliubovCreator h m c s branches (Bosonize.A07Interactions.oppositeOrientation η)) = 0 := …
```


## Bosonize/Core/Ch01LatticeBand.lean

```lean
def inBandPredicate (L : ℕ) (k : ℤ) : Prop := -(L : ℤ) < 2 * k ∧ 2 * k ≤ (L : ℤ)

abbrev Band (L : ℕ) := {k : ℤ // inBandPredicate L k}
```


## Bosonize/Core/Ch14Mandelstam.lean

```lean
lemma projected_map_apply (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ) (A : A05.Operators σ h) (v : A05.jointBudget h Ns Kin) : (projectedMap h Ns Nt Kin Kout A v : A05.FockSpace σ h) = projection h Nt Kout (A v) := …

lemma physical_occupation_expansion (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kout : ℕ) (S : A05.Occupation σ h) : projection h (Ch13.lowerCharge Ns ν) Kout (A05.liftedAnnihilation h b ν x (A02.ket S)) = (A01.normalization (2*h) : ℂ) • ∑ k : Ch01.Band (2*h), if (ν,k) ∈ S then (Ch06Ext.twistedCharacter (2*h) (b ν) k x * Ch04.fermionSign (ν,k) S) • projection h (Ch13.lowerCharge Ns ν) Kout (A02.ket (S.erase (ν,k))) else 0 := …

lemma physical_ground_expansion (h : ℕ) (hh : 0<h) (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (ν : σ) (x : ℤ) (Kin Kout : ℕ) : (physicalMap h b Ns ν x Kin Kout (groundVector h hh Ns hN Kin) : A05.FockSpace σ h) = (A01.normalization (2*h) : ℂ) • ∑ k : Ch01.Band (2*h), if (ν,k) ∈ A05.groundConfiguration h Ns then (Ch06Ext.twistedCharacter (2*h) (b ν) k x * Ch04.fermionSign (ν,k) (A05.groundConfiguration h Ns)) • projection h (Ch13.lowerCharge Ns ν) Kout (A02.ket ((A05.groundConfiguration h Ns).erase (ν,k))) else 0 := …
```


## Bosonize/Core/Ch15DualFields.lean

```lean
theorem zero_mode_obstruction_on_ground (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hmargin : A06.branchMargins h M K Ns branches) (x : ZMod (2 * h)) (c : ℂ) (hc : c ≠ 0) : ¬ (∀ y : ZMod (2 * h), A02.commutator (phiField h M ζ branches x) (A06.opForwardDiff h (thetaField h M ζ branches) y) (A05.groundKet h Ns) = (c * A06.dirichletKernel h M ζ x y) • A05.groundKet h Ns) := …
```


## Bosonize/Core/A04CurrentMargins.lean

```lean
lemma action_on_budget (h : ℕ) (N K : ℤ) (A B : Ch09.Operators h) (hab : ∀ S : Ch07.Occupation h, Ch07.relativeCharge h S = N → Ch07.excitationEnergy h S ≤ K → A (A02.ket S) = B (A02.ket S)) : ∀ v ∈ Ch07.fixedBudget h N K, A v = B v := …
```


## Bosonize/Core/Ch10Heisenberg.lean

```lean
lemma rho_empty_commutator (h m : ℕ) : A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (m : ℤ)) (A02.ket (∅ : Ch07.Occupation h)) = 0 := …
```


## Bosonize/Core/A04DensityKinematics.lean

```lean
lemma edge_support (L : ℕ) (m n : ℤ) (p k : Ch01.Band L) (he : edgeMatrix L m n p k ≠ 0) : p.val = k.val+(m+n) ∧ (Ch01.inBandPredicate L (k.val+n) ↔ ¬ Ch01.inBandPredicate L (k.val+m)) := …

lemma opposite_shift_entry (L : ℕ) (m : ℤ) (p k : Ch01.Band L) : edgeMatrix L (-m) m p k = if p = k then (if Ch01.inBandPredicate L (k.val+m) then (1:ℂ) else 0) - (if Ch01.inBandPredicate L (k.val-m) then (1:ℂ) else 0) else 0 := …
```


## Bosonize/Core/Ch16FieldHamiltonian.lean

```lean
lemma chiral_spatial_collapse_on_budget (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hmargin : A06.marginAt h M K Ns (A06.speciesOf branches η)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : (∑ x : ZMod (2 * h), chiralSquare h M ζ branches η x) v = ((2 : ℂ) • (∑ m ∈ Finset.Icc 1 M, epsilon h ζ m • (A05.rho h (A06.speciesOf branches η) (m : ℤ) * A05.rho h (A06.speciesOf branches η) (-(m : ℤ))))) v := …

lemma excited_ket_mem_budget (h K m : ℕ) (hh : 0 < h) (hm : m ≤ K) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (branches : A06.Branches σ) (η : A06.Orientation) : excitedKet h Ns branches η m ∈ A05.jointBudget h Ns K := …

lemma excited_ket_nonzero (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (branches : A06.Branches σ) (η : A06.Orientation) (hmargin : A06.marginAt h M m Ns (A06.speciesOf branches η)) : excitedKet h Ns branches η m ≠ 0 := …
```
