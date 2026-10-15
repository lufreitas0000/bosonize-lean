# CH18 Core API closure (frozen Core; proofs omitted)

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

def commutator (A B : Module.End ℂ V) : Module.End ℂ V := A * B - B * A
```


## Bosonize/Core/A03EnergyBudgets.lean

```lean
abbrev Operators (ι : Type*) [Fintype ι] [DecidableEq ι] := Module.End ℂ (A02.FockSpace ι)

noncomputable def coordinateSpace (U : Set (A02.Occupation ι)) : Submodule ℂ (A02.FockSpace ι) :=
  Submodule.span ℂ (A02.ket '' U)

lemma ket_mem_coordinate_space (U : Set (A02.Occupation ι)) (S : A02.Occupation ι) : A02.ket S ∈ coordinateSpace U ↔ S ∈ U := …
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

lemma species_joint_configuration (h : ℕ) (Ss : σ → Ch07.Occupation h) (ν : σ) : Ch07.speciesConfiguration h (jointConfiguration h Ss) ν = Ss ν := …

lemma joint_species_configuration (h : ℕ) (S : Occupation σ h) : jointConfiguration h (fun ν => Ch07.speciesConfiguration h S ν) = S := …

lemma tensor_kets (h : ℕ) (Ss : σ → Ch07.Occupation h) : tensorVector h (fun ν => A02.ket (Ss ν)) = A02.ket (jointConfiguration h Ss) := …

lemma preceding_count_split (h : ℕ) (ν : σ) (k : Ch01.Band (2*h)) (S : Occupation σ h) : Ch04.precedingCount (ν,k) S = (∑ η ∈ Finset.univ.filter (· < ν), (Ch07.speciesConfiguration h S η).card) + Ch04.precedingCount k (Ch07.speciesConfiguration h S ν) := …

lemma annihilation_car (h : ℕ) (i j : Mode σ h) : A02.anticommutator (annihilation h i.1 i.2) (annihilation h j.1 j.2) = 0 := …

lemma creation_car (h : ℕ) (i j : Mode σ h) : A02.anticommutator (creation h i.1 i.2) (creation h j.1 j.2) = 0 := …

lemma mixed_car (h : ℕ) (i j : Mode σ h) : A02.anticommutator (annihilation h i.1 i.2) (creation h j.1 j.2) = (if i=j then (1 : ℂ) else 0) • (1 : Operators σ h) := …

lemma rho_adjoint (h : ℕ) (ν : σ) (m : ℤ) : LinearMap.adjoint (rho h ν m) = rho h ν (-m) := …

lemma rho_cross_commute (h : ℕ) (ν η : σ) (hne : ν ≠ η) (m n : ℤ) : A02.commutator (rho h ν m) (rho h η n) = 0 := …

lemma rho_budget_map (h : ℕ) (ν : σ) (m : ℤ) (Ns : σ → ℤ) (K : ℕ) (v : FockSpace σ h) (hv : v ∈ jointBudget h Ns K) : rho h ν m v ∈ Ch07.speciesBudget h Ns ((K : ℤ)+m) := …

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

lemma joint_signed_current_commutator (h K : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (m n : ℤ) (hmargin : |m| + |n| + (K : ℤ) + |Ns ν| ≤ (h : ℤ)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (A05.rho h ν m) (A05.rho h ν n) v = Ch10.schwingerCoefficient m n • v := …

lemma chiral_same_commutator_on_budget (h M K : ℕ) (hh : 0 < h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : Branches σ) (η : Orientation) (Ns : σ → ℤ) (hmargin : marginAt h M K Ns (speciesOf branches η)) (x y : ZMod (2 * h)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (chiralField h M ζ branches η x) (chiralField h M ζ branches η y) v = ((orientationSign η : ℂ) * skewKernel h M ζ x y) • v := …

lemma concrete_two_branch_parameters : ∃ (h M K : ℕ) (Ns : Fin 2 → ℤ) (branches : Branches (Fin 2)), 0 < h ∧ 1 ≤ M ∧ 2 * M < 2 * h ∧ A05.admissible h Ns ∧ branchMargins h M K Ns branches ∧ A05.groundKet h Ns ∈ A05.jointBudget h Ns K ∧ A05.groundKet h Ns ≠ 0 := …
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

noncomputable def computationalMomentum (h : ℕ) (ν : σ) :
    A05.Operators σ h :=
  ∑ k : Ch01.Band (2 * h), (k.val : ℂ) • seaSubtractedNumber h ν k

noncomputable def speciesCurrentIntra (h M : ℕ) (ν : σ) :
    A05.Operators σ h :=
  (2 : ℂ) • (∑ m ∈ Finset.Icc 1 M,
    A05.rho h ν (m : ℤ) * A05.rho h ν (-(m : ℤ))) +
    A05.chargeObservable h ν * A05.chargeObservable h ν

noncomputable def currentIntraBranch (h M : ℕ) (g4 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  ((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) •
    (speciesCurrentIntra h M branches.rightSpecies +
      speciesCurrentIntra h M branches.leftSpecies)

noncomputable def pairingInterBranch (h M : ℕ) (g2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  ((g2 : ℂ) / ((2 * h : ℕ) : ℂ)) •
    (A05.chargeObservable h r * A05.chargeObservable h l +
      ∑ m ∈ Finset.Icc 1 M,
        (A05.rho h r (m : ℤ) * A05.rho h l (m : ℤ) +
          A05.rho h r (-(m : ℤ)) * A05.rho h l (-(m : ℤ))))

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

noncomputable def dressedModeNumber (h m : ℕ) (u c s : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  (u : ℂ) • (bogoliubovCreator h m c s branches .right *
      bogoliubovAnnihilator h m c s branches .right +
    bogoliubovCreator h m c s branches .left *
      bogoliubovAnnihilator h m c s branches .left)

lemma species_raw_intra_eq_current_sub_correction (h M : ℕ) (ν : σ) : speciesRawIntra h M ν = speciesCurrentIntra h M ν - seaWickCorrection h M ν := …

theorem raw_intra_eq_current_sub_correction (h M : ℕ) (g4 : ℝ) (branches : A06.Branches σ) : rawIntraBranch h M g4 branches = currentIntraBranch h M g4 branches - ((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) • (seaWickCorrection h M branches.rightSpecies + seaWickCorrection h M branches.leftSpecies) := …

lemma sea_wick_correction_full_band (h M : ℕ) (hh : 0 < h) (hM : h - 1 ≤ M) (ν : σ) : seaWickCorrection h M ν = (2 : ℂ) • computationalMomentum h ν - A05.chargeObservable h ν := …

lemma hopping_mode_kills_ground (h m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (branches : A06.Branches σ) : (A05.rho h branches.rightSpecies (m : ℤ) * A05.rho h branches.leftSpecies (-(m : ℤ)) + A05.rho h branches.rightSpecies (-(m : ℤ)) * A05.rho h branches.leftSpecies (m : ℤ)) (A05.groundKet h Ns) = 0 := …

lemma pairing_mode_ground_nonzero (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (branches : A06.Branches σ) (hmargin : A06.branchMargins h M m Ns branches) : (A05.rho h branches.rightSpecies (m : ℤ) * A05.rho h branches.leftSpecies (m : ℤ) + A05.rho h branches.rightSpecies (-(m : ℤ)) * A05.rho h branches.leftSpecies (-(m : ℤ))) (A05.groundKet h Ns) ≠ 0 := …

lemma pairing_mode_self_adjoint (h m : ℕ) (v1 v2 : ℝ) (branches : A06.Branches σ) : LinearMap.adjoint (pairingMode h m v1 v2 branches) = pairingMode h m v1 v2 branches := …

lemma bogoliubov_creator_adjoint (h m : ℕ) (c s : ℝ) (branches : A06.Branches σ) (η : A06.Orientation) : LinearMap.adjoint (bogoliubovCreator h m c s branches η) = bogoliubovAnnihilator h m c s branches η := …

theorem bogoliubov_expansion_on_budget (h M K m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (v1 v2 : ℝ) (hp : HyperbolicParams v1 v2) (branches : A06.Branches σ) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : dressedModeNumber h m hp.u hp.c hp.s branches v = pairingMode h m v1 v2 branches v + ((2 * hp.u * hp.s ^ 2 * (m : ℝ) : ℝ) : ℂ) • v := …

theorem bogoliubov_ccr_on_budget (h M K m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (bogoliubovAnnihilator h m c s branches η) (bogoliubovCreator h m c s branches η) v = (m : ℂ) • v := …
```


## Bosonize/Core/Ch05Fermions.lean

```lean
abbrev FockSpace (L : ℕ) := A02.FockSpace (Ch01.Band L)

abbrev Operators (L : ℕ) := Module.End ℂ (FockSpace L)
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

lemma ground_configuration_charge (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) : relativeCharge h (groundConfiguration h N) = N := …

lemma charge_observable_ket (h : ℕ) (S : Occupation h) : chargeObservable h (A02.ket S) = (relativeCharge h S : ℂ) • A02.ket S := …

def speciesConfiguration (h : ℕ) (S : A02.Occupation (σ × Ch01.Band (2*h))) (ν : σ) : Occupation h :=
  (S.filter (fun p => p.1 = ν)).image Prod.snd

def totalExcitation (h : ℕ) (S : A02.Occupation (σ × Ch01.Band (2*h))) : ℤ :=
  ∑ ν : σ, excitationEnergy h (speciesConfiguration h S ν)

noncomputable def speciesBudget (h : ℕ) (Ns : σ → ℤ) (K : ℤ) :
    Submodule ℂ (A02.FockSpace (σ × Ch01.Band (2*h))) :=
  A03.coordinateSpace {S | (∀ ν, relativeCharge h (speciesConfiguration h S ν) = Ns ν) ∧
    totalExcitation h S ≤ K}

lemma total_excitation_nonneg (h : ℕ) (hh : 0 < h) (S : A02.Occupation (σ × Ch01.Band (2*h))) : 0 ≤ totalExcitation h S := …

lemma species_budget_ket (h : ℕ) (S : A02.Occupation (σ × Ch01.Band (2*h))) (Ns : σ → ℤ) (K : ℤ) : A02.ket S ∈ speciesBudget h Ns K ↔ (∀ ν, relativeCharge h (speciesConfiguration h S ν) = Ns ν) ∧ totalExcitation h S ≤ K := …
```


## Bosonize/Core/Ch08Boson.lean

```lean
abbrev Mode (M : ℕ) := Fin M

abbrev Polynomial (M : ℕ) := MvPolynomial (Mode M) ℂ

abbrev Operators (M : ℕ) := Module.End ℂ (Polynomial M)

noncomputable def creation (M : ℕ) (i : Mode M) : Operators M :=
  LinearMap.mulLeft ℂ (MvPolynomial.X i)

noncomputable def annihilation (M : ℕ) (i : Mode M) : Operators M :=
  (weight M i : ℂ) • derivative M i

noncomputable def commutator (M : ℕ) (A B : Operators M) : Operators M :=
  A * B - B * A

theorem creation_pairing_adjoint (M : ℕ) (i : Mode M) (p q : Polynomial M) : pairing M (creation M i p) q = pairing M p (annihilation M i q) := …

theorem ccr (M : ℕ) (i j : Mode M) : commutator M (annihilation M i) (creation M j) = if i = j then (weight M i : ℂ) • (1 : Operators M) else 0 := …
```


## Bosonize/Core/Ch09DensityModes.lean

```lean
abbrev FockSpace (h : ℕ) := Ch07.FockSpace h

abbrev Operators (h : ℕ) := Module.End ℂ (FockSpace h)

noncomputable def rho (h : ℕ) (m : ℤ) : Operators h :=
  A04.dGamma (A04.shift (2*h) m)

lemma rho_valid_pairs (h : ℕ) (m : ℤ) : rho h m = ∑ z ∈ A04.validPairs (2*h) m, Ch04.hopping z.1 z.2 := …

lemma rho_adjoint (h : ℕ) (m : ℤ) : LinearMap.adjoint (rho h m) = rho h (-m) := …

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

lemma ground_top_annihilation (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (ν : σ) (hν : -(h : ℤ)+1 ≤ Ns ν) (k : Ch01.Band (2*h)) (hk : k.val=Ns ν) : A05.annihilation h ν k (A05.groundKet h Ns) = kleinPhase h Ns ν • A05.groundKet h (lowerCharge Ns ν) := …
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

theorem field_weighted_on_budget (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : fieldHamiltonian h M ζ branches v = ((4 : ℂ) • weightedEnergy h M ζ branches) v := …

lemma error_weighted_on_budget (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : errorOperator h M ζ branches v = ((4 : ℂ) • weightedError h M ζ branches) v := …

lemma ground_error_zero (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hmargin : A06.branchMargins h M K Ns branches) : errorOperator h M ζ branches (A05.groundKet h Ns) = 0 := …

lemma excited_ket_mem_budget (h K m : ℕ) (hh : 0 < h) (hm : m ≤ K) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (branches : A06.Branches σ) (η : A06.Orientation) : excitedKet h Ns branches η m ∈ A05.jointBudget h Ns K := …

lemma excited_ket_nonzero (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (branches : A06.Branches σ) (η : A06.Orientation) (hmargin : A06.marginAt h M m Ns (A06.speciesOf branches η)) : excitedKet h Ns branches η m ≠ 0 := …

theorem single_mode_error_eigenvector (h M K m : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (hm : 1 ≤ m) (hcut : m ≤ M) (hK : m ≤ K) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hmargin : A06.branchMargins h M K Ns branches) : errorOperator h M ζ branches (excitedKet h Ns branches η m) = ((4 : ℂ) * (m : ℂ) * (epsilon h ζ m - referenceWeight h ζ)) • excitedKet h Ns branches η m := …

theorem first_mode_error_zero (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hK : 1 ≤ K) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hmargin : A06.branchMargins h M K Ns branches) : errorOperator h M ζ branches (excitedKet h Ns branches η 1) = 0 := …

theorem error_nonzero_witness (h M K m : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (hm : 1 ≤ m) (hcut : m ≤ M) (hK : m ≤ K) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (hweight : epsilon h ζ m ≠ referenceWeight h ζ) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hmargin : A06.branchMargins h M K Ns branches) : excitedKet h Ns branches η m ≠ 0 ∧ errorOperator h M ζ branches (excitedKet h Ns branches η m) ≠ 0 := …

theorem concrete_dispersion_gap : epsilon 8 (A01.canonicalRoot 16) 2 ≠ referenceWeight 8 (A01.canonicalRoot 16) := …

theorem concrete_excited_error_witness : A05.admissible 8 (fun _ : Fin 2 => 0) ∧ A06.branchMargins 8 2 2 (fun _ : Fin 2 => 0) standardBranches ∧ excitedKet 8 (fun _ : Fin 2 => 0) standardBranches .right 2 ≠ 0 ∧ errorOperator 8 2 (A01.canonicalRoot 16) standardBranches (excitedKet 8 (fun _ : Fin 2 => 0) standardBranches .right 2) ≠ 0 := …
```


## Bosonize/Core/Ch17LuttingerModels.lean

```lean
noncomputable def v1Velocity (vF g4 : ℝ) : ℝ :=
  vF + g4 / (2 * Real.pi)

noncomputable def v2Velocity (g2 : ℝ) : ℝ :=
  g2 / (2 * Real.pi)

def sugawaraMargin {σ : Type*} (h M K : ℕ) (Ns : σ → ℤ)
    (branches : A06.Branches σ) : Prop :=
  K ≤ M ∧
    (K : ℤ) + |Ns branches.rightSpecies| < (h : ℤ) ∧
    (K : ℤ) + |Ns branches.leftSpecies| < (h : ℤ)

noncomputable def zeroModeEnergyScalar {σ : Type*} (h : ℕ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) : ℝ :=
  let L : ℝ := ((2 * h : ℕ) : ℝ)
  let nr : ℝ := (Ns branches.rightSpecies : ℝ)
  let nl : ℝ := (Ns branches.leftSpecies : ℝ)
  (2 * Real.pi * vF / L) * (nr * (nr + 1) / 2 + nl * (nl + 1) / 2) +
    (g4 / (2 * L)) * (nr ^ 2 + nl ^ 2) +
    (g2 / L) * nr * nl -
    mu * (nr + nl)

lemma zero_mode_scalar_canonical_mu {σ : Type*} (h : ℕ) (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) : zeroModeEnergyScalar h vF g4 g2 (canonicalMu h vF) branches Ns = symmetricZeroModeScalar h vF g4 g2 branches Ns := …

noncomputable def chemicalPotentialOp (h : ℕ) (mu : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  (mu : ℂ) • (A05.chargeObservable h branches.rightSpecies +
    A05.chargeObservable h branches.leftSpecies)

noncomputable def freeFermionKinetic (h : ℕ) (vF : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let prefactor : ℂ := ((2 * Real.pi * vF : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ)
  prefactor •
    (A07Interactions.computationalMomentum h branches.rightSpecies +
      A07Interactions.computationalMomentum h branches.leftSpecies)

noncomputable def luttingerOscillatorOp (h M : ℕ) (vF g4 g2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  (((2 * Real.pi : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ)) •
    ∑ m ∈ Finset.Icc 1 M,
      A07Interactions.pairingMode h m
        (v1Velocity vF g4) (v2Velocity g2) branches

noncomputable def luttingerFermionChosenModel (h M : ℕ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) :
    A05.Operators σ h :=
  freeFermionKinetic h vF branches +
    A07Interactions.currentIntraBranch h M g4 branches +
    A07Interactions.pairingInterBranch h M g2 branches -
    chemicalPotentialOp h mu branches

theorem luttinger_chosen_eq_bosonized (h M : ℕ) (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) : luttingerChosenModel h M vF g4 g2 mu branches = luttingerBosonizedHamiltonian h M vF g4 g2 mu branches := …

lemma zero_mode_op_on_budget (h K : ℕ) (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : zeroModeEnergyOp h vF g4 g2 mu branches v = (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v := …

theorem free_fermion_eq_sugawara_on_budget (h M K : ℕ) (hh : 0 < h) (vF : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hSug : sugawaraMargin h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : freeFermionKinetic h vF branches v = freeSugawaraKinetic h M vF branches v := …

theorem luttinger_hamiltonian_on_budget (h M K : ℕ) (hh : 0 < h) (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hSug : sugawaraMargin h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : luttingerFermionChosenModel h M vF g4 g2 mu branches v = luttingerOscillatorOp h M vF g4 g2 branches v + (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v := …

theorem luttinger_hamiltonian_canonical_mu_on_budget (h M K : ℕ) (hh : 0 < h) (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hSug : sugawaraMargin h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : luttingerFermionChosenModel h M vF g4 g2 (canonicalMu h vF) branches v = luttingerOscillatorOp h M vF g4 g2 branches v + (symmetricZeroModeScalar h vF g4 g2 branches Ns : ℂ) • v := …

theorem luttinger_raw_intra_on_budget (h M K : ℕ) (hh : 0 < h) (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hSug : sugawaraMargin h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : (freeFermionKinetic h vF branches + A07Interactions.rawIntraBranch h M g4 branches + A07Interactions.pairingInterBranch h M g2 branches - chemicalPotentialOp h mu branches) v = luttingerOscillatorOp h M vF g4 g2 branches v + (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v - (((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) • (A07Interactions.seaWickCorrection h M branches.rightSpecies + A07Interactions.seaWickCorrection h M branches.leftSpecies)) v := …

theorem concrete_luttinger_witness : let Ns : Fin 2 → ℤ := fun _ => 0 A05.admissible 8 Ns ∧ A06.branchMargins 8 2 2 Ns Ch16.standardBranches ∧ sugawaraMargin 8 2 2 Ns Ch16.standardBranches ∧ A05.groundKet 8 Ns ∈ A05.jointBudget 8 Ns 2 ∧ A05.groundKet 8 Ns ≠ 0 ∧ luttingerBosonizedHamiltonian 8 2 1 (6 * Real.pi) (6 * Real.pi) (canonicalMu 8 1) Ch16.standardBranches (A05.groundKet 8 Ns) ≠ 0 := …
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
noncomputable def creation (i : ι) : Module.End ℂ (A02.FockSpace ι) :=
  A02.extendBasis fun S =>
    if i ∈ S then 0 else fermionSign i S • A02.ket (insert i S)

noncomputable def annihilation (i : ι) : Module.End ℂ (A02.FockSpace ι) :=
  A02.extendBasis fun S =>
    if i ∈ S then fermionSign i S • A02.ket (S.erase i) else 0

noncomputable def hopping (i j : ι) : Module.End ℂ (A02.FockSpace ι) :=
  creation i * annihilation j

lemma creation_square (i : ι) : creation i * creation i = 0 := …

lemma annihilation_square (i : ι) : annihilation i * annihilation i = 0 := …

lemma creation_adjoint_pairing (i : ι) (S T : A02.Occupation ι) : inner ℂ (A02.ket S) (annihilation i (A02.ket T)) = inner ℂ (creation i (A02.ket S)) (A02.ket T) := …

lemma annihilation_car (i j : ι) : A02.anticommutator (annihilation i) (annihilation j) = 0 := …

lemma creation_car (i j : ι) : A02.anticommutator (creation i) (creation j) = 0 := …

lemma mixed_car (i j : ι) : A02.anticommutator (annihilation i) (creation j) = (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ (A02.FockSpace ι)) := …
```


## Bosonize/Core/Ch06Ext.lean

```lean
noncomputable def annihilation (b : BoundaryTwist L) (n : ℤ) : Ch05.Operators L :=
  liftPhase L b n • Ch05.positionAnnihilation L (n : Ch01.Lattice L)

noncomputable def creation (b : BoundaryTwist L) (n : ℤ) : Ch05.Operators L :=
  star (liftPhase L b n) • Ch05.positionCreation L (n : Ch01.Lattice L)
```


## Bosonize/Core/A07FiniteNormalOrdering.lean

```lean
lemma normal_pair_contraction (h M : ℕ) (branches : A06.Branches σ) (p q : Letter M) : normalPair h M branches p q - rawPair h M branches p q = if p.2.2 = false ∧ q.2.2 = true then A02.commutator (current h M branches q) (current h M branches p) else 0 := …

lemma contraction_on_joint_budget (h M K : ℕ) (hh : 0 < h) (branches : A06.Branches σ) (Ns : σ → ℤ) (p q : Letter M) (hp : p.2.2 = false) (hq : q.2.2 = true) (hbranch : p.1 = q.1) (hmargin : A06.marginAt h M K Ns (A06.speciesOf branches (orientation p.1))) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : (normalPair h M branches p q - rawPair h M branches p q) v = (if natMode p = natMode q then -(natMode p : ℂ) else 0) • v := …
```


## Bosonize/Core/Ch15DualFields.lean

```lean
lemma phi_self_commutator_on_budget (h M K : ℕ) (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (x y : ZMod (2 * h)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (phiField h M ζ branches x) (phiField h M ζ branches y) v = 0 := …

lemma theta_self_commutator_on_budget (h M K : ℕ) (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (x y : ZMod (2 * h)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (thetaField h M ζ branches x) (thetaField h M ζ branches y) v = 0 := …

lemma mixed_commutator_on_budget (h M K : ℕ) (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (x y : ZMod (2 * h)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (phiField h M ζ branches x) (thetaField h M ζ branches y) v = (2 * A06.skewKernel h M ζ x y) • v := …

lemma mixed_forward_diff_on_budget (h M K : ℕ) (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (x y : ZMod (2 * h)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (phiField h M ζ branches x) (A06.opForwardDiff h (thetaField h M ζ branches) y) v = (2 * A06.opForwardDiff h (A06.skewKernel h M ζ x) y) • v := …

theorem zero_mode_obstruction_on_ground (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hmargin : A06.branchMargins h M K Ns branches) (x : ZMod (2 * h)) (c : ℂ) (hc : c ≠ 0) : ¬ (∀ y : ZMod (2 * h), A02.commutator (phiField h M ζ branches x) (A06.opForwardDiff h (thetaField h M ζ branches) y) (A05.groundKet h Ns) = (c * A06.dirichletKernel h M ζ x y) • A05.groundKet h Ns) := …
```


## Bosonize/Core/Ch14Mandelstam.lean

```lean
lemma physical_ground_expansion (h : ℕ) (hh : 0<h) (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (ν : σ) (x : ℤ) (Kin Kout : ℕ) : (physicalMap h b Ns ν x Kin Kout (groundVector h hh Ns hN Kin) : A05.FockSpace σ h) = (A01.normalization (2*h) : ℂ) • ∑ k : Ch01.Band (2*h), if (ν,k) ∈ A05.groundConfiguration h Ns then (Ch06Ext.twistedCharacter (2*h) (b ν) k x * Ch04.fermionSign (ν,k) (A05.groundConfiguration h Ns)) • projection h (Ch13.lowerCharge Ns ν) Kout (A02.ket ((A05.groundConfiguration h Ns).erase (ν,k))) else 0 := …
```


## Bosonize/Core/A04CurrentMargins.lean

```lean
lemma action_on_budget (h : ℕ) (N K : ℤ) (A B : Ch09.Operators h) (hab : ∀ S : Ch07.Occupation h, Ch07.relativeCharge h S = N → Ch07.excitationEnergy h S ≤ K → A (A02.ket S) = B (A02.ket S)) : ∀ v ∈ Ch07.fixedBudget h N K, A v = B v := …
```


## Bosonize/Core/A01FourierCharacters.lean

```lean
lemma root_ne_zero (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) : ζ ≠ 0 := …

lemma residue_character_int_cast (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) : residueCharacter L ζ (k : Ch01.Lattice L) (x : Ch01.Lattice L) = integerCharacter ζ k x := …

lemma character_sum (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Lattice L) : (∑ x : Ch01.Lattice L, residueCharacter L ζ k x) = if k = 0 then (L : K) else 0 := …

lemma canonical_root_primitive (L : ℕ) [NeZero L] : IsPrimitiveRoot (canonicalRoot L) L := …
```
