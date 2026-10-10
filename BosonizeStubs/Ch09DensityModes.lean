module

public import BosonizeStubs.A04DensityKinematics
public import Bosonize.Core.Ch07VacuumBudget
public import Bosonize.Core.Ch06Ext

/-!
# CH09 actual finite fermionic density modes
Phase A: complete data and one-sorry review targets.
The oscillator representation of CH08 is not used to define these fermionic operators.
Twisted Fourier reconstruction is retained explicitly; site density Fourier coefficients
are cyclic, whereas the partial currents below retain nonwrapping integer transfer.
-/
@[expose] public section
namespace Bosonize.Ch09
open scoped BigOperators Classical

/-- Actual finite Fock space, identical to CH05 and CH07 for L=2h. -/
abbrev FockSpace (h : ℕ) := Ch07.FockSpace h

/-- Ambient complex endomorphisms; multiplication applies the right factor first. -/
abbrev Operators (h : ℕ) := Module.End ℂ (FockSpace h)

/-- Raw nonwrapping current, obtained from the concrete CAR bilinears by the actual partial shift matrix. -/
noncomputable def rho (h : ℕ) (m : ℤ) : Operators h :=
  A04.dGamma (A04.shift (2*h) m)

/-- Sea-normal-ordered density removes h particles only at zero transfer. It is not a change of shift carrier. -/
noncomputable def normalRho (h : ℕ) (m : ℤ) : Operators h :=
  rho h m - (if m = 0 then (h : ℂ) • 1 else 0)

/-- Particle-hole pairs that act nontrivially on the fixed sea: occupied source and empty target. -/
def activeSeaPairs (h : ℕ) (m : ℤ) : Finset (Ch01.Band (2*h) × Ch01.Band (2*h)) :=
  (A04.validPairs (2*h) m).filter (fun z => z.2.val ≤ 0 ∧ 0 < z.1.val)

/-- Occupation produced by the indicated hop from the fixed sea; used only with active-pair hypotheses. -/
def hopConfiguration (h : ℕ) (z : Ch01.Band (2*h) × Ch01.Band (2*h)) : Ch07.Occupation h :=
  insert z.1 ((Ch05.seaConfiguration (2*h)).erase z.2)

/-- Actual CAR sign of first removing the occupied source and then creating the empty target. -/
def hopSign (h : ℕ) (z : Ch01.Band (2*h) × Ch01.Band (2*h)) : ℂ :=
  Ch04.fermionSign z.2 (Ch05.seaConfiguration (2*h)) *
    Ch04.fermionSign z.1 ((Ch05.seaConfiguration (2*h)).erase z.2)

/-- Positive current labels 1,...,h. The empty family at h=0 causes no false existence assertion. -/
abbrev PositiveMode (h : ℕ) := {m : ℕ // 1 ≤ m ∧ m ≤ h}

/-- The physical linear-dispersion Hamiltonian with an explicitly retained real momentum offset β.
Choose b=angleTwist (2h) β when connecting this energy model to a boundary field. -/
noncomputable def physicalHamiltonian (h : ℕ) (β : ℝ) : Operators h :=
  Ch05.bareHamiltonian (2*h) + (β : ℂ) • Ch05.totalNumber (2*h)

section TwistDictionary
variable (L : ℕ) [NeZero L]

/-- Reconstruct momentum annihilation from the chosen twisted field and the conjugate matching Fourier kernel.
The same b occurs in both factors; this is a concrete finite transform, not an assumed dictionary. -/
noncomputable def reconstructedAnnihilation (b : Ch06Ext.BoundaryTwist L)
    (k : Ch01.Band L) : Ch05.Operators L :=
  (A01.normalization L : ℂ) • ∑ x : Ch01.Lattice L,
    star (Ch06Ext.twistedCharacter L b k (x.val : ℤ)) •
      Ch06Ext.siteAnnihilation L b x

/-- The actual adjoint of the reconstructed annihilator, so creator kernel conjugation is automatic. -/
noncomputable def reconstructedCreation (b : Ch06Ext.BoundaryTwist L)
    (k : Ch01.Band L) : Ch05.Operators L :=
  LinearMap.adjoint (reconstructedAnnihilation L b k)

/-- Truncate reconstructed twisted momentum pairs by integer transfer before summing.
This is the appropriate physical-field dictionary for nonwrapping density modes. -/
noncomputable def reconstructedDensity (b : Ch06Ext.BoundaryTwist L) (m : ℤ) : Ch05.Operators L :=
  ∑ z ∈ A04.validPairs L m,
    reconstructedCreation L b z.1 * reconstructedAnnihilation L b z.2

/-- Discrete Fourier coefficient of the full local density, using the positive character for transfer m.
Its finite lattice coefficient is cyclic and includes aliases at band edges. -/
noncomputable def siteFourierDensity (b : Ch06Ext.BoundaryTwist L) (m : ℤ) : Ch05.Operators L :=
  ∑ x : Ch01.Lattice L,
    A01.integerCharacter (A01.canonicalRoot L) m (x.val : ℤ) •
      Ch06Ext.density L b (x.val : ℤ)

/-- Exact cyclic alias remainder: all congruent transfers except the requested integer transfer.
This records edge wrapping explicitly instead of equating cyclic and partial shifts. -/
noncomputable def wrapRemainder (m : ℤ) : Ch05.Operators L :=
  ∑ p : Ch01.Band L, ∑ k : Ch01.Band L,
    (if (p.val-k.val : Ch01.Lattice L) = (m : Ch01.Lattice L) ∧ p.val ≠ k.val+m
      then (1 : ℂ) else 0) • Ch04.hopping p k

/-- Matching twisted inverse Fourier transform recovers the original concrete momentum annihilator. -/
lemma reconstructed_annihilation (b : Ch06Ext.BoundaryTwist L) (k : Ch01.Band L) :
    reconstructedAnnihilation L b k = Ch05.momentumAnnihilation L k := by sorry

/-- Taking the actual adjoint recovers the concrete momentum creator with its correct conjugate phase. -/
lemma reconstructed_creation (b : Ch06Ext.BoundaryTwist L) (k : Ch01.Band L) :
    reconstructedCreation L b k = Ch05.momentumCreation L k := by sorry

/-- The integer-truncated physical-field dictionary equals second quantization of the partial shift for every twist. -/
lemma reconstructed_density (b : Ch06Ext.BoundaryTwist L) (m : ℤ) :
    reconstructedDensity L b m = A04.dGamma (A04.shift L m) := by sorry

/-- The untruncated site Fourier coefficient contains the exact cyclic wrap remainder.
This distinction cannot be removed globally, even in the periodic boundary sector. -/
lemma site_fourier_dictionary (b : Ch06Ext.BoundaryTwist L) (m : ℤ) :
    siteFourierDensity L b m = A04.dGamma (A04.shift L m) + wrapRemainder L m := by sorry

/-- Local-density Fourier coefficients are independent of the external scalar twist after conjugate phases cancel. -/
lemma site_fourier_twist_independent (b c : Ch06Ext.BoundaryTwist L) (m : ℤ) :
    siteFourierDensity L b m = siteFourierDensity L c m := by sorry
end TwistDictionary

/-- The matrix lift is exactly the original filtered sum of momentum CAR bilinears. -/
lemma rho_valid_pairs (h : ℕ) (m : ℤ) :
    rho h m = ∑ z ∈ A04.validPairs (2*h) m, Ch04.hopping z.1 z.2 := by sorry

/-- Zero transfer counts all particles, independently of the sea subtraction. -/
lemma rho_zero (h : ℕ) :
    rho h 0 = Ch05.totalNumber (2*h) := by sorry

/-- Zero normal-ordered transfer is the existing relative-charge observable. -/
lemma normal_rho_zero (h : ℕ) :
    normalRho h 0 = Ch07.chargeObservable h := by sorry

/-- Nonzero transfers have no sea subtraction. -/
lemma normal_rho_nonzero (h : ℕ) (m : ℤ) (hm : m ≠ 0) :
    normalRho h m = rho h m := by sorry

/-- Transfers outside the actual diameter have no valid source-target pair. -/
lemma rho_vanish (h : ℕ) (m : ℤ) (hm : (2*h : ℕ) ≤ m.natAbs) :
    rho h m = 0 := by sorry

/-- Density adjoint reverses the transfer, as inherited from the true CAR adjoints. -/
lemma rho_adjoint (h : ℕ) (m : ℤ) :
    LinearMap.adjoint (rho h m) = rho h (-m) := by sorry

/-- Sea subtraction is real and occurs equally for transfer zero and its negative. -/
lemma normal_rho_adjoint (h : ℕ) (m : ℤ) :
    LinearMap.adjoint (normalRho h m) = normalRho h (-m) := by sorry

/-- Same-sign positive modes commute globally, without imposing a budget margin. -/
lemma rho_positive_commute (h : ℕ) (m n : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n) :
    A02.commutator (rho h m) (rho h n) = 0 := by sorry

/-- Same-sign negative modes also commute on the entire finite Fock space. -/
lemma rho_negative_commute (h : ℕ) (m n : ℤ) (hm : m ≤ 0) (hn : n ≤ 0) :
    A02.commutator (rho h m) (rho h n) = 0 := by sorry

/-- All density commutators lift their exact finite one-particle edge matrices. -/
lemma rho_commutator_edge (h : ℕ) (m n : ℤ) :
    A02.commutator (rho h m) (rho h n) = A04.dGamma (A04.edgeMatrix (2*h) m n) := by sorry

/-- Each density hop conserves total particle number. -/
lemma rho_number_commutator (h : ℕ) (m : ℤ) :
    A02.commutator (Ch05.totalNumber (2*h)) (rho h m) = 0 := by sorry

/-- Integer transfer shifts the bare linear-dispersion energy by exactly m. -/
lemma rho_bare_energy_commutator (h : ℕ) (m : ℤ) :
    A02.commutator (Ch05.bareHamiltonian (2*h)) (rho h m) = (m : ℂ) • rho h m := by sorry

/-- Subtracting sea energy leaves density covariance unchanged. -/
lemma rho_shifted_energy_commutator (h : ℕ) (m : ℤ) :
    A02.commutator (Ch05.shiftedHamiltonian (2*h)) (rho h m) = (m : ℂ) • rho h m := by sorry

/-- The β number term cancels because the density conserves charge; the Hamiltonian itself retains β. -/
lemma rho_physical_energy_commutator (h : ℕ) (β : ℝ) (m : ℤ) :
    A02.commutator (physicalHamiltonian h β) (rho h m) = (m : ℂ) • rho h m := by sorry

/-- Equal external momentum offsets cancel in a source-target transfer. -/
lemma physical_transfer (L : ℕ) (β : ℝ) (p k : Ch01.Band L) (m : ℤ) (hp : p.val = k.val+m) :
    Ch06Ext.physicalMomentum L β p - Ch06Ext.physicalMomentum L β k = (m : ℝ) := by sorry

/-- Concrete density action preserves charge and shifts excitation energy exactly, including blocked hops. -/
lemma rho_exact_shift (h : ℕ) (m : ℤ) :
    A03.ExactShift (Ch07.relativeCharge h) (Ch07.excitationEnergy h) (rho h m) 0 m := by sorry

/-- The sector ground-energy polynomial cancels because charge is unchanged. -/
lemma rho_excitation_commutator (h : ℕ) (m : ℤ) :
    A02.commutator (Ch07.excitationObservable h) (rho h m) = (m : ℂ) • rho h m := by sorry

/-- Signed transfer maps the actual coordinate budget into the correctly shifted target budget. -/
lemma rho_budget_map (h : ℕ) (m N K : ℤ) :
    ∀ v ∈ Ch07.fixedBudget h N K, rho h m v ∈ Ch07.fixedBudget h N (K+m) := by sorry

/-- A lowering transfer below the nonnegative excitation floor annihilates every input in the budget. -/
lemma rho_lowering_budget_zero (h : ℕ) (hh : 0 < h) (m N K : ℤ) (hKm : K-m < 0) :
    ∀ v ∈ Ch07.fixedBudget h N K, rho h (-m) v = 0 := by sorry

/-- Every positive lowering mode annihilates each admissible sector ground, including the empty and full endpoints. -/
lemma rho_lowering_ground (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : Ch07.admissible h N) (m : ℤ) (hm : 0 < m) :
    rho h (-m) (Ch07.groundKet h N hN) = 0 := by sorry

/-- The sea has exactly h occupied modes; zero transfer normalization is fixed independently of scalar CCR. -/
lemma rho_zero_sea (h : ℕ) (hh : 0 < h) :
    rho h 0 (Ch07.vacuumKet h) = (h : ℂ) • Ch07.vacuumKet h := by sorry

/-- Normal ordering zeros the relative-charge vacuum. -/
lemma normal_rho_sea_zero (h : ℕ) (hh : 0 < h) :
    normalRho h 0 (Ch07.vacuumKet h) = 0 := by sorry

/-- The first excited vacuum action is an explicit signed sum of allowed occupation hops. -/
lemma rho_sea_hop_sum (h : ℕ) (m : ℤ) (hm : 0 < m) :
    rho h m (Ch07.vacuumKet h) = ∑ z ∈ activeSeaPairs h m, hopSign h z • A02.ket (hopConfiguration h z) := by sorry

/-- For 1≤m≤h the occupied sources are exactly 1−m,...,0, giving precisely m allowed hops. -/
lemma active_sea_pairs_card (h m : ℕ) (hm : 1 ≤ m) (hmh : m ≤ h) :
    (activeSeaPairs h (m : ℤ)).card = m := by sorry

/-- The resulting configuration uniquely determines its removed hole and added particle, ruling out sum cancellation. -/
lemma hop_configuration_injective (h : ℕ) (m : ℤ) (z w : Ch01.Band (2*h) × Ch01.Band (2*h)) (hz : z ∈ activeSeaPairs h m) (hw : w ∈ activeSeaPairs h m) (he : hopConfiguration h z = hopConfiguration h w) :
    z = w := by sorry

/-- Both actual CAR signs have modulus one, so every allowed hop contributes unit squared norm. -/
lemma hop_sign_norm (h : ℕ) (z : Ch01.Band (2*h) × Ch01.Band (2*h)) :
    ‖hopSign h z‖ = 1 := by sorry

/-- Orthogonal occupation hops establish the first exact norm without importing any Schwinger relation. -/
lemma rho_sea_norm_sq (h m : ℕ) (hm : 1 ≤ m) (hmh : m ≤ h) :
    ‖rho h (m : ℤ) (Ch07.vacuumKet h)‖^2 = (m : ℝ) := by sorry

/-- The positive norm supplies a concrete non-vacuity witness for each retained positive density mode. -/
lemma rho_sea_ne_zero (h m : ℕ) (hm : 1 ≤ m) (hmh : m ≤ h) :
    rho h (m : ℤ) (Ch07.vacuumKet h) ≠ 0 := by sorry

/-- Density excitations have relative energy m; the bare Hamiltonian instead has sea energy plus m. -/
lemma rho_sea_energy (h : ℕ) (m : ℤ) :
    Ch05.shiftedHamiltonian (2*h) (rho h m (Ch07.vacuumKet h)) = (m : ℂ) • rho h m (Ch07.vacuumKet h) := by sorry

/-- Distinct positive transfers have orthogonal vacuum excitations, by distinct energy or disjoint hop support. -/
lemma rho_sea_orthogonal (h : ℕ) (m n : PositiveMode h) (hmn : m ≠ n) :
    inner ℂ (rho h (m.val : ℤ) (Ch07.vacuumKet h)) (rho h (n.val : ℤ) (Ch07.vacuumKet h)) = 0 := by sorry

/-- Orthogonality and the directly proved nonzero action give linear independence of the positive excitations. -/
lemma rho_sea_linear_independent (h : ℕ) :
    LinearIndependent ℂ (fun m : PositiveMode h => rho h (m.val : ℤ) (Ch07.vacuumKet h)) := by sorry

/-- Evaluate a linear relation at the sea to transfer excitation independence to actual endomorphisms. -/
lemma rho_linear_independent (h : ℕ) :
    LinearIndependent ℂ (fun m : PositiveMode h => rho h (m.val : ℤ)) := by sorry

/-- Covariant transport of a number-conserving density cancels the external step phase.
The remaining root phase depends on transfer m and the chosen translation orientation. -/
lemma rho_transport (h : ℕ) [NeZero (2*h)] (b : Ch06Ext.BoundaryTwist (2*h))
    (m n : ℤ) :
    Ch06Ext.transport (2*h) b n (rho h m) =
      A01.integerCharacter (A01.canonicalRoot (2*h)) (-m) n • rho h m := by sorry

end Bosonize.Ch09
