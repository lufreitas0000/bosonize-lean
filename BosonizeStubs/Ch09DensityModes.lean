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
    reconstructedAnnihilation L b k = Ch05.momentumAnnihilation L k := by
  exact (Ch06Ext.twisted_fourier_inverse L b k).symm

/-- Taking the actual adjoint recovers the concrete momentum creator with its correct conjugate phase. -/
lemma reconstructed_creation (b : Ch06Ext.BoundaryTwist L) (k : Ch01.Band L) :
    reconstructedCreation L b k = Ch05.momentumCreation L k := by
  rw [reconstructedCreation, reconstructed_annihilation]
  exact (Ch04.creation_eq_adjoint k).symm

/-- The integer-truncated physical-field dictionary equals second quantization of the partial shift for every twist. -/
lemma reconstructed_density (b : Ch06Ext.BoundaryTwist L) (m : ℤ) :
    reconstructedDensity L b m = A04.dGamma (A04.shift L m) := by
  simp only [reconstructedDensity, reconstructed_creation, reconstructed_annihilation,
    A04.dGamma, A04.shift, A04.validPairs, Finset.sum_filter, ite_smul,
    one_smul, zero_smul, Ch04.hopping, Ch05.momentumCreation, Ch05.momentumAnnihilation]
  exact Fintype.sum_prod_type _

/-- The untruncated site Fourier coefficient contains the exact cyclic wrap remainder.
This distinction cannot be removed globally, even in the periodic boundary sector. -/
lemma site_fourier_dictionary (b : Ch06Ext.BoundaryTwist L) (m : ℤ) :
    siteFourierDensity L b m = A04.dGamma (A04.shift L m) + wrapRemainder L m := by
  have hn := A01.root_ne_zero L _ (A01.canonical_root_primitive L)
  have hsum (j : ℤ) :
      (∑ x : Ch01.Lattice L,
        A01.integerCharacter (A01.canonicalRoot L) j (x.val : ℤ)) =
      if (j : Ch01.Lattice L) = 0 then (L : ℂ) else 0 := by
    have he (x : Ch01.Lattice L) :
        A01.integerCharacter (A01.canonicalRoot L) j (x.val : ℤ) =
        A01.residueCharacter L (A01.canonicalRoot L) (j : Ch01.Lattice L) x := by
      simpa using (A01.residue_character_int_cast L _
        (A01.canonical_root_primitive L) j (x.val : ℤ)).symm
    simp_rw [he]
    exact A01.character_sum L _ (A01.canonical_root_primitive L) _
  have hc (x : Ch01.Lattice L) (p k : Ch01.Band L) :
      A01.integerCharacter (A01.canonicalRoot L) m (x.val : ℤ) *
       (((A01.normalization L : ℂ) *
          A01.integerCharacter (A01.canonicalRoot L) (-p.val) (x.val : ℤ)) *
        ((A01.normalization L : ℂ) *
          A01.bandCharacter L (A01.canonicalRoot L) k x)) =
      (A01.normalization L : ℂ)^2 *
        A01.integerCharacter (A01.canonicalRoot L) (m-p.val+k.val) (x.val : ℤ) := by
    unfold A01.bandCharacter A01.integerCharacter
    calc
      _ = (A01.normalization L : ℂ)^2 *
          (A01.canonicalRoot L^(m*(x.val : ℤ)) *
           A01.canonicalRoot L^(-p.val*(x.val : ℤ)) *
           A01.canonicalRoot L^(k.val*(x.val : ℤ))) := by ring
      _ = _ := by
        rw [← zpow_add₀ hn, ← zpow_add₀ hn]
        congr 2
        ring
  simp only [siteFourierDensity, Ch06Ext.density_untwisted, Int.cast_natCast,
    ZMod.natCast_zmod_val, Ch05.positionNumber, Ch05.positionCreation,
    Ch05.positionAnnihilation, Finset.smul_sum, Finset.sum_mul, Finset.mul_sum,
    smul_mul_smul_comm, smul_smul]
  simp_rw [hc]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ (α := Ch01.Lattice L))]
  simp_rw [← Finset.sum_smul, ← Finset.mul_sum, hsum]
  rw [Finset.sum_comm]
  unfold A04.dGamma A04.shift wrapRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hz : ((m-p.val+k.val : ℤ) : Ch01.Lattice L) = 0 ↔
      (p.val-k.val : Ch01.Lattice L) = (m : Ch01.Lattice L) := by
    push_cast
    constructor <;> intro h <;> linear_combination -h
  simp only [hz]
  by_cases hi : p.val = k.val+m
  · have hr : (p.val-k.val : Ch01.Lattice L) = (m : Ch01.Lattice L) := by
      rw [hi]
      push_cast
      ring
    simp only [hr]
    simp only [hi, ite_true, ne_eq, not_true_eq_false, and_false,
      ite_false, zero_smul, add_zero, one_smul]
    rw [mul_comm, A01.normalization_square_complex, one_smul]
    rfl
  · by_cases hr : (p.val-k.val : Ch01.Lattice L) = (m : Ch01.Lattice L)
    · simp only [hi, hr, ite_true, ite_false, ne_eq, not_false_eq_true,
        and_self, zero_smul, zero_add, one_smul]
      rw [mul_comm, A01.normalization_square_complex, one_smul]
      rfl
    · simp [hi, hr]


/-- Local-density Fourier coefficients are independent of the external scalar twist after conjugate phases cancel. -/
lemma site_fourier_twist_independent (b c : Ch06Ext.BoundaryTwist L) (m : ℤ) :
    siteFourierDensity L b m = siteFourierDensity L c m := by
  simp only [siteFourierDensity, Ch06Ext.density_untwisted]
end TwistDictionary

/-- The matrix lift is exactly the original filtered sum of momentum CAR bilinears. -/
lemma rho_valid_pairs (h : ℕ) (m : ℤ) :
    rho h m = ∑ z ∈ A04.validPairs (2*h) m, Ch04.hopping z.1 z.2 := by
  simp only [rho, A04.dGamma, A04.shift, A04.validPairs,
    Finset.sum_filter, ite_smul, one_smul, zero_smul]
  exact (Fintype.sum_prod_type (fun z : Ch01.Band (2*h) × Ch01.Band (2*h) =>
    if z.1.val = z.2.val+m then Ch04.hopping z.1 z.2 else 0)).symm

/-- Zero transfer counts all particles, independently of the sea subtraction. -/
lemma rho_zero (h : ℕ) :
    rho h 0 = Ch05.totalNumber (2*h) := by
  unfold rho
  convert A04.dGamma_identity (ι := Ch01.Band (2*h)) using 1
  · congr 1
    ext p k
    simp [A04.shift, Matrix.one_apply, Subtype.ext_iff]
  · simp [Ch05.totalNumber, Ch05.momentumNumber, Ch05.momentumCreation,
      Ch05.momentumAnnihilation, Ch04.totalNumber, Ch04.number]

/-- Zero normal-ordered transfer is the existing relative-charge observable. -/
lemma normal_rho_zero (h : ℕ) :
    normalRho h 0 = Ch07.chargeObservable h := by
  simp only [normalRho, ite_true, rho_zero]
  exact (Ch07.charge_observable_total_number h).symm

/-- Nonzero transfers have no sea subtraction. -/
lemma normal_rho_nonzero (h : ℕ) (m : ℤ) (hm : m ≠ 0) :
    normalRho h m = rho h m := by
  simp [normalRho, hm]

/-- Transfers outside the actual diameter have no valid source-target pair. -/
lemma rho_vanish (h : ℕ) (m : ℤ) (hm : (2*h : ℕ) ≤ m.natAbs) :
    rho h m = 0 := by
  rw [rho, A04.shift_vanish, A04.dGamma_zero]
  simpa only [Int.natCast_natAbs] using
    (show ((2*h : ℕ) : ℤ) ≤ (m.natAbs : ℤ) from by exact_mod_cast hm)

/-- Density adjoint reverses the transfer, as inherited from the true CAR adjoints. -/
lemma rho_adjoint (h : ℕ) (m : ℤ) :
    LinearMap.adjoint (rho h m) = rho h (-m) := by
  simp only [rho, A04.dGamma_adjoint, A04.shift_adjoint]

/-- Sea subtraction is real and occurs equally for transfer zero and its negative. -/
lemma normal_rho_adjoint (h : ℕ) (m : ℤ) :
    LinearMap.adjoint (normalRho h m) = normalRho h (-m) := by
  by_cases hm : m = 0
  · subst m
    rw [normal_rho_zero, Ch07.charge_observable_adjoint]
    simp only [neg_zero, normal_rho_zero]
  · rw [normal_rho_nonzero h m hm, normal_rho_nonzero h (-m) (neg_ne_zero.mpr hm), rho_adjoint]

/-- Same-sign positive modes commute globally, without imposing a budget margin. -/
lemma rho_positive_commute (h : ℕ) (m n : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n) :
    A02.commutator (rho h m) (rho h n) = 0 := by
  rw [rho, rho, A04.dGamma_commutator, A04.shift_mul_nonnegative _ m n hm hn,
    A04.shift_mul_nonnegative _ n m hn hm, add_comm n m, sub_self, A04.dGamma_zero]

/-- Same-sign negative modes also commute on the entire finite Fock space. -/
lemma rho_negative_commute (h : ℕ) (m n : ℤ) (hm : m ≤ 0) (hn : n ≤ 0) :
    A02.commutator (rho h m) (rho h n) = 0 := by
  rw [rho, rho, A04.dGamma_commutator, A04.shift_mul_nonpositive _ m n hm hn,
    A04.shift_mul_nonpositive _ n m hn hm, add_comm n m, sub_self, A04.dGamma_zero]

/-- All density commutators lift their exact finite one-particle edge matrices. -/
lemma rho_commutator_edge (h : ℕ) (m n : ℤ) :
    A02.commutator (rho h m) (rho h n) = A04.dGamma (A04.edgeMatrix (2*h) m n) := by
  rw [rho, rho, A04.dGamma_commutator, A04.shift_commutator_edge]

/-- Each density hop conserves total particle number. -/
lemma rho_number_commutator (h : ℕ) (m : ℤ) :
    A02.commutator (Ch05.totalNumber (2*h)) (rho h m) = 0 := by
  rw [← rho_zero h]
  by_cases hm : 0 ≤ m
  · exact rho_positive_commute h 0 m (by omega) hm
  · exact rho_negative_commute h 0 m (by omega) (by omega)

/-- Integer transfer shifts the bare linear-dispersion energy by exactly m. -/
lemma rho_bare_energy_commutator (h : ℕ) (m : ℤ) :
    A02.commutator (Ch05.bareHamiltonian (2*h)) (rho h m) = (m : ℂ) • rho h m := by
 have hp (H A B : Operators h) : A02.commutator H (A*B) =
   A02.commutator H A * B + A * A02.commutator H B := by
   unfold A02.commutator
   noncomm_ring
 have hh (p k : Ch01.Band (2*h)) :
   A02.commutator (Ch05.bareHamiltonian (2*h)) (Ch04.hopping p k) =
   ((p.val : ℂ)-(k.val : ℂ)) • Ch04.hopping p k := by
   change A02.commutator (Ch05.bareHamiltonian (2*h))
     (Ch05.momentumCreation (2*h) p * Ch05.momentumAnnihilation (2*h) k) = _
   rw [hp, Ch05.bare_creation_commutator, Ch05.bare_annihilation_commutator]
   simp [sub_eq_add_neg, add_smul, Ch04.hopping,
     Ch05.momentumCreation, Ch05.momentumAnnihilation]
 have hs (f : Ch01.Band (2*h) × Ch01.Band (2*h) → Operators h) (s) :
   A02.commutator (Ch05.bareHamiltonian (2*h)) (∑ z ∈ s, f z) =
   ∑ z ∈ s, A02.commutator (Ch05.bareHamiltonian (2*h)) (f z) := by
   simp [A02.commutator, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
 rw [rho_valid_pairs, hs, Finset.smul_sum]
 apply Finset.sum_congr rfl
 intro z hz
 rw [hh]
 have hm := (A04.mem_valid_pairs (2*h) m z.1 z.2).mp hz
 have hc : (z.1.val : ℂ)-(z.2.val : ℂ) = (m : ℂ) := by exact_mod_cast (show z.1.val-z.2.val=m by omega)
 rw [hc]

/-- Subtracting sea energy leaves density covariance unchanged. -/
lemma rho_shifted_energy_commutator (h : ℕ) (m : ℤ) :
    A02.commutator (Ch05.shiftedHamiltonian (2*h)) (rho h m) = (m : ℂ) • rho h m := by
 rw [Ch05.shiftedHamiltonian]
 simp only [A02.commutator, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
   one_mul, mul_one]
 have hb := rho_bare_energy_commutator h m
 unfold A02.commutator at hb
 convert hb using 1; abel

/-- The β number term cancels because the density conserves charge; the Hamiltonian itself retains β. -/
lemma rho_physical_energy_commutator (h : ℕ) (β : ℝ) (m : ℤ) :
    A02.commutator (physicalHamiltonian h β) (rho h m) = (m : ℂ) • rho h m := by
 have hb := rho_bare_energy_commutator h m
 have hn := rho_number_commutator h m
 simp only [physicalHamiltonian, A02.commutator, add_mul, mul_add,
   smul_mul_assoc, mul_smul_comm]
 unfold A02.commutator at hb hn
 have hc := sub_eq_zero.mp hn
 rw [hc]
 convert hb using 1; abel

/-- Equal external momentum offsets cancel in a source-target transfer. -/
lemma physical_transfer (L : ℕ) (β : ℝ) (p k : Ch01.Band L) (m : ℤ) (hp : p.val = k.val+m) :
    Ch06Ext.physicalMomentum L β p - Ch06Ext.physicalMomentum L β k = (m : ℝ) := by
  unfold Ch06Ext.physicalMomentum
  have hp' : (p.val : ℝ) = (k.val : ℝ) + (m : ℝ) := by exact_mod_cast hp
  linarith

/-- Concrete density action preserves charge and shifts excitation energy exactly, including blocked hops. -/
lemma rho_exact_shift (h : ℕ) (m : ℤ) :
    A03.ExactShift (Ch07.relativeCharge h) (Ch07.excitationEnergy h) (rho h m) 0 m := by
 intro S
 have hn (k : Ch01.Band (2*h)) : Ch05.momentumNumber (2*h) k (A02.ket S) =
   (if k ∈ S then (1 : ℂ) else 0) • A02.ket S := by
   convert Ch04.number_ket k S using 1
   all_goals simp [Ch05.momentumNumber, Ch05.momentumCreation, Ch05.momentumAnnihilation, Ch04.number, Ch05.FockSpace, A02.ket, A02.occupationBasis, A02.occupationONB]
 have hb (p k : Ch01.Band (2*h)) (hb : k ∉ S ∨ (p ≠ k ∧ p ∈ S)) :
   (Ch05.momentumCreation (2*h) p * Ch05.momentumAnnihilation (2*h) k) (A02.ket S) = 0 := by
   convert Ch04.hopping_blocked p k S hb using 1
   all_goals simp [Ch05.momentumCreation, Ch05.momentumAnnihilation, Ch04.hopping, Ch05.FockSpace, A02.ket, A02.occupationBasis, A02.occupationONB]
 have ha (p k : Ch01.Band (2*h)) (hp : p ∉ S) (hk : k ∈ S) (hpk : p ≠ k) :
   (Ch05.momentumCreation (2*h) p * Ch05.momentumAnnihilation (2*h) k) (A02.ket S) =
    (Ch04.fermionSign k S * Ch04.fermionSign p (S.erase k)) • A02.ket (insert p (S.erase k)) := by
   convert Ch04.hopping_ket p k S hpk hp hk using 1
   all_goals simp [Ch05.momentumCreation, Ch05.momentumAnnihilation, Ch04.hopping, Ch05.FockSpace, A02.ket, A02.occupationBasis, A02.occupationONB]
   congr 2
   · congr 1
     ext i
     simp only [Finset.mem_erase]
   · ext i
     simp only [Finset.mem_insert, Finset.mem_erase]
 rw [rho_valid_pairs]
 simp only [LinearMap.sum_apply]
 apply Submodule.sum_mem
 intro z hz
 change (Ch05.momentumCreation (2*h) z.1 * Ch05.momentumAnnihilation (2*h) z.2) (A02.ket S) ∈ _
 have hpair := (A04.mem_valid_pairs (2*h) m z.1 z.2).mp hz
 by_cases hj : z.2 ∈ S
 · by_cases hi : z.1 = z.2
   · have hm : m=0 := by rw [hi] at hpair; omega
     subst m
     rw [hi]
     change Ch05.momentumNumber (2*h) z.2 (A02.ket S) ∈ _
     rw [hn]
     simp only [hj, ite_true, one_smul]
     apply (A03.ket_mem_coordinate_space _ S).mpr
     simp
   · by_cases hp : z.1 ∈ S
     · rw [hb z.1 z.2 (Or.inr ⟨hi,hp⟩)]
       exact Submodule.zero_mem _
     · rw [ha z.1 z.2 hp hj hi]
       apply Submodule.smul_mem
       apply (A03.ket_mem_coordinate_space _ _).mpr
       have hp' : z.1 ∉ S.erase z.2 := fun hx => hp (Finset.mem_of_mem_erase hx)
       constructor
       · rw [Ch07.charge_insert h _ _ hp', Ch07.charge_erase h _ _ hj]
         omega
       · rw [Ch07.excitation_insert h _ _ hp', Ch07.excitation_erase h _ _ hj,
           Ch07.charge_erase h _ _ hj]
         omega
 · rw [hb z.1 z.2 (Or.inl hj)]
   exact Submodule.zero_mem _

/-- The sector ground-energy polynomial cancels because charge is unchanged. -/
lemma rho_excitation_commutator (h : ℕ) (m : ℤ) :
    A02.commutator (Ch07.excitationObservable h) (rho h m) = (m : ℂ) • rho h m := by
 exact A03.exact_shift_energy_commutator _ _ _ 0 m (rho_exact_shift h m)

/-- Signed transfer maps the actual coordinate budget into the correctly shifted target budget. -/
lemma rho_budget_map (h : ℕ) (m N K : ℤ) :
    ∀ v ∈ Ch07.fixedBudget h N K, rho h m v ∈ Ch07.fixedBudget h N (K+m) := by
 exact Ch07.charge_preserving_budget_map h (rho h m) m N K
  (A03.exact_shift_filtered _ _ _ 0 m (rho_exact_shift h m))

/-- A lowering transfer below the nonnegative excitation floor annihilates every input in the budget. -/
lemma rho_lowering_budget_zero (h : ℕ) (hh : 0 < h) (m N K : ℤ) (hKm : K-m < 0) :
    ∀ v ∈ Ch07.fixedBudget h N K, rho h (-m) v = 0 := by
 apply Ch07.negative_shift_annihilates h hh (rho h (-m)) 0 (-m) N K
 · exact A03.exact_shift_filtered _ _ _ 0 (-m) (rho_exact_shift h (-m))
 · omega

/-- Every positive lowering mode annihilates each admissible sector ground, including the empty and full endpoints. -/
lemma rho_lowering_ground (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : Ch07.admissible h N) (m : ℤ) (hm : 0 < m) :
    rho h (-m) (Ch07.groundKet h N hN) = 0 := by
 exact rho_lowering_budget_zero h hh m N 0 (by omega) _
  (Ch07.ground_ket_mem_budget h hh N hN 0)

/-- The sea has exactly h occupied modes; zero transfer normalization is fixed independently of scalar CCR. -/
lemma rho_zero_sea (h : ℕ) (hh : 0 < h) :
    rho h 0 (Ch07.vacuumKet h) = (h : ℂ) • Ch07.vacuumKet h := by
  rw [rho_zero]
  change Ch05.totalNumber (2*h) (A02.ket (Ch05.seaConfiguration (2*h))) = _
  rw [Ch05.total_number_ket, Ch05.sea_card_even h hh]
  rfl

/-- Normal ordering zeros the relative-charge vacuum. -/
lemma normal_rho_sea_zero (h : ℕ) (hh : 0 < h) :
    normalRho h 0 (Ch07.vacuumKet h) = 0 := by
  simp [normalRho, rho_zero_sea h hh]

/-- The first excited vacuum action is an explicit signed sum of allowed occupation hops. -/
lemma rho_sea_hop_sum (h : ℕ) (m : ℤ) (hm : 0 < m) :
    rho h m (Ch07.vacuumKet h) = ∑ z ∈ activeSeaPairs h m, hopSign h z • A02.ket (hopConfiguration h z) := by
  rw [rho_valid_pairs, LinearMap.sum_apply]
  have happ (z : Ch01.Band (2*h) × Ch01.Band (2*h))
      (hz : z ∈ A04.validPairs (2*h) m)
      (hc : z.2.val ≤ 0 ∧ 0 < z.1.val) :
      Ch04.hopping z.1 z.2 (Ch07.vacuumKet h) =
        hopSign h z • A02.ket (hopConfiguration h z) := by
    have hij : z.1 ≠ z.2 := by
      intro he
      have hv := congrArg Subtype.val he
      omega
    have hi : z.1 ∉ Ch05.seaConfiguration (2*h) := by
      simp [Ch05.seaConfiguration, not_le.mpr hc.2]
    have hj : z.2 ∈ Ch05.seaConfiguration (2*h) := by
      simp [Ch05.seaConfiguration, hc.1]
    convert Ch04.hopping_ket z.1 z.2 (Ch05.seaConfiguration (2*h)) hij hi hj using 1
    all_goals simp [Ch07.vacuumKet, Ch05.seaKet, hopSign, hopConfiguration,
      A02.ket, A02.occupationBasis, A02.occupationONB]
    all_goals congr!
  have hblocked (z : Ch01.Band (2*h) × Ch01.Band (2*h))
      (hz : z ∈ A04.validPairs (2*h) m)
      (hc : ¬ (z.2.val ≤ 0 ∧ 0 < z.1.val)) :
      Ch04.hopping z.1 z.2 (Ch07.vacuumKet h) = 0 := by
    have hv : z.1.val = z.2.val+m := by simpa [A04.validPairs] using hz
    have hb : z.2 ∉ Ch05.seaConfiguration (2*h) ∨
        (z.1 ≠ z.2 ∧ z.1 ∈ Ch05.seaConfiguration (2*h)) := by
      by_cases hs : z.2.val ≤ 0
      · right
        constructor
        · intro he
          have he' := congrArg Subtype.val he
          omega
        · simp [Ch05.seaConfiguration]
          omega
      · left
        simp [Ch05.seaConfiguration, hs]
    convert Ch04.hopping_blocked z.1 z.2 (Ch05.seaConfiguration (2*h)) hb using 1
    all_goals simp [Ch07.vacuumKet, Ch05.seaKet, A02.ket,
      A02.occupationBasis, A02.occupationONB]
  simp only [activeSeaPairs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hc : z.2.val ≤ 0 ∧ 0 < z.1.val
  · rw [ite_eq_left hc]
    exact happ z hz hc
  · rw [ite_eq_right hc]
    exact hblocked z hz hc

/-- For 1≤m≤h the occupied sources are exactly 1−m,...,0, giving precisely m allowed hops. -/
lemma active_sea_pairs_card (h m : ℕ) (hm : 1 ≤ m) (hmh : m ≤ h) :
    (activeSeaPairs h (m : ℤ)).card = m := by
  classical
  have hmem (z : Ch01.Band (2*h) × Ch01.Band (2*h)) :
      z ∈ activeSeaPairs h (m : ℤ) ↔
      z.1.val = z.2.val + (m : ℤ) ∧ z.2.val ≤ 0 ∧ 0 < z.1.val := by
    simp [activeSeaPairs, A04.validPairs]
  have hin (z : Ch01.Band (2*h) × Ch01.Band (2*h)) (hz : z ∈ activeSeaPairs h (m : ℤ)) :
      (-z.2.val).toNat ∈ Finset.range m := by
    have hz' := (hmem z).mp hz
    simp only [Finset.mem_range]
    omega
  have hinj (z w : Ch01.Band (2*h) × Ch01.Band (2*h))
      (hz : z ∈ activeSeaPairs h (m : ℤ)) (hw : w ∈ activeSeaPairs h (m : ℤ))
      (he : (-z.2.val).toNat = (-w.2.val).toNat) : z = w := by
    have hz' := (hmem z).mp hz
    have hw' := (hmem w).mp hw
    apply Prod.ext <;> apply Subtype.ext <;> omega
  have hsurj (n : ℕ) (hn : n ∈ Finset.range m) :
      ∃ z, ∃ hz : z ∈ activeSeaPairs h (m : ℤ), (-z.2.val).toNat = n := by
    have hn' : n < m := Finset.mem_range.mp hn
    have hs : Ch01.inBandPredicate (2*h) (-(n : ℤ)) := by
      simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat]
      omega
    have ht : Ch01.inBandPredicate (2*h) ((m : ℤ) - n) := by
      simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat]
      omega
    refine ⟨(⟨(m : ℤ)-n, ht⟩, ⟨-(n : ℤ), hs⟩), ?_, ?_⟩
    · apply (hmem _).mpr
      dsimp
      omega
    · simp
  simpa using Finset.card_bij (fun z _ => (-z.2.val).toNat) hin
    (fun z hz w hw => hinj z w hz hw) hsurj

/-- The resulting configuration uniquely determines its removed hole and added particle, ruling out sum cancellation. -/
lemma hop_configuration_injective (h : ℕ) (m : ℤ) (z w : Ch01.Band (2*h) × Ch01.Band (2*h)) (hz : z ∈ activeSeaPairs h m) (hw : w ∈ activeSeaPairs h m) (he : hopConfiguration h z = hopConfiguration h w) :
    z = w := by
  have hz' : z.1.val = z.2.val+m ∧ z.2.val ≤ 0 ∧ 0 < z.1.val := by
    simpa [activeSeaPairs, A04.validPairs, and_assoc] using hz
  have hw' : w.1.val = w.2.val+m ∧ w.2.val ≤ 0 ∧ 0 < w.1.val := by
    simpa [activeSeaPairs, A04.validPairs, and_assoc] using hw
  have hne : z.1 ∉ Ch05.seaConfiguration (2*h) := by
    simp [Ch05.seaConfiguration, not_le.mpr hz'.2.2]
  have hp : z.1 = w.1 := by
    by_contra hn
    have hmem : z.1 ∈ insert w.1 ((Ch05.seaConfiguration (2*h)).erase w.2) := by
      change z.1 ∈ hopConfiguration h w
      rw [← he]
      exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hmem with hyes | hyes
    · exact hn hyes
    · exact hne (Finset.mem_of_mem_erase hyes)
  apply Prod.ext hp
  apply Subtype.ext
  have hv := congrArg Subtype.val hp
  omega

/-- Both actual CAR signs have modulus one, so every allowed hop contributes unit squared norm. -/
lemma hop_sign_norm (h : ℕ) (z : Ch01.Band (2*h) × Ch01.Band (2*h)) :
    ‖hopSign h z‖ = 1 := by
  simp [hopSign, Ch04.fermionSign, norm_pow]

/-- Orthogonal occupation hops establish the first exact norm without importing any Schwinger relation. -/
lemma rho_sea_norm_sq (h m : ℕ) (hm : 1 ≤ m) (hmh : m ≤ h) :
    ‖rho h (m : ℤ) (Ch07.vacuumKet h)‖^2 = (m : ℝ) := by
  classical
  rw [rho_sea_hop_sum h (m : ℤ) (by exact_mod_cast (show 0 < m by omega))]
  let v := fun z : Ch01.Band (2*h) × Ch01.Band (2*h) =>
    hopSign h z • A02.ket (hopConfiguration h z)
  have ho : ∀ z ∈ activeSeaPairs h (m : ℤ), ∀ w ∈ activeSeaPairs h (m : ℤ),
      inner ℂ (v z) (v w) = if z = w then 1 else 0 := by
    intro z hz w hw
    dsimp [v]
    rw [inner_smul_left, inner_smul_right, A02.ket_inner]
    by_cases he : z = w
    · subst w
      simp only [↓reduceIte, mul_one]
      simp only [hopSign, map_mul, Ch04.fermion_sign_conj]
      calc
        _ = (Ch04.fermionSign z.2 (Ch05.seaConfiguration (2*h)) *
             Ch04.fermionSign z.2 (Ch05.seaConfiguration (2*h))) *
          (Ch04.fermionSign z.1 ((Ch05.seaConfiguration (2*h)).erase z.2) *
             Ch04.fermionSign z.1 ((Ch05.seaConfiguration (2*h)).erase z.2)) := by ring
        _ = 1 := by rw [Ch04.fermion_sign_square, Ch04.fermion_sign_square]; simp
    · have hcfg : hopConfiguration h z ≠ hopConfiguration h w := by
        intro hh
        exact he (hop_configuration_injective h (m : ℤ) z w hz hw hh)
      simp [he, hcfg]
  have hi : inner ℂ (∑ z ∈ activeSeaPairs h (m : ℤ), v z)
      (∑ z ∈ activeSeaPairs h (m : ℤ), v z) =
        ((activeSeaPairs h (m : ℤ)).card : ℂ) := by
    simp only [sum_inner, inner_sum]
    have hh : ∀ w ∈ activeSeaPairs h (m : ℤ),
        (∑ z ∈ activeSeaPairs h (m : ℤ), inner ℂ (v z) (v w)) = 1 := by
      intro w hw
      rw [Finset.sum_congr rfl (fun z hz => ho z hz w hw)]
      simp [hw]
    rw [Finset.sum_congr rfl hh]
    simp
  rw [active_sea_pairs_card h m hm hmh] at hi
  have hr := congrArg (RCLike.re : ℂ → ℝ) hi
  simpa [v, ← Complex.ofReal_pow] using hr

/-- The positive norm supplies a concrete non-vacuity witness for each retained positive density mode. -/
lemma rho_sea_ne_zero (h m : ℕ) (hm : 1 ≤ m) (hmh : m ≤ h) :
    rho h (m : ℤ) (Ch07.vacuumKet h) ≠ 0 := by
  intro he
  have hn := rho_sea_norm_sq h m hm hmh
  rw [he, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hn
  have hp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  linarith

/-- Density excitations have relative energy m; the bare Hamiltonian instead has sea energy plus m. -/
lemma rho_sea_energy (h : ℕ) (m : ℤ) :
    Ch05.shiftedHamiltonian (2*h) (rho h m (Ch07.vacuumKet h)) = (m : ℂ) • rho h m (Ch07.vacuumKet h) := by
  have hc := congrArg (fun A : Operators h => A (Ch07.vacuumKet h))
    (rho_shifted_energy_commutator h m)
  simpa [A02.commutator, Module.End.mul_apply, Ch07.vacuumKet,
    Ch05.shifted_hamiltonian_sea] using hc

/-- Distinct positive transfers have orthogonal vacuum excitations, by distinct energy or disjoint hop support. -/
lemma rho_sea_orthogonal (h : ℕ) (m n : PositiveMode h) (hmn : m ≠ n) :
    inner ℂ (rho h (m.val : ℤ) (Ch07.vacuumKet h)) (rho h (n.val : ℤ) (Ch07.vacuumKet h)) = 0 := by
  have hi := LinearMap.adjoint_inner_left (Ch05.shiftedHamiltonian (2*h))
    (rho h (n.val : ℤ) (Ch07.vacuumKet h)) (rho h (m.val : ℤ) (Ch07.vacuumKet h))
  rw [Ch05.shifted_hamiltonian_adjoint, rho_sea_energy, rho_sea_energy] at hi
  simp only [inner_smul_left, inner_smul_right, map_intCast] at hi
  have hne : (m.val : ℂ) ≠ (n.val : ℂ) := by
    intro he
    apply hmn
    apply Subtype.ext
    exact_mod_cast he
  have hh : ((m.val : ℂ) - (n.val : ℂ)) *
      inner ℂ (rho h (m.val : ℤ) (Ch07.vacuumKet h))
        (rho h (n.val : ℤ) (Ch07.vacuumKet h)) = 0 := by
    rw [sub_mul]
    exact sub_eq_zero.mpr hi
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hne)

/-- Orthogonality and the directly proved nonzero action give linear independence of the positive excitations. -/
lemma rho_sea_linear_independent (h : ℕ) :
    LinearIndependent ℂ (fun m : PositiveMode h => rho h (m.val : ℤ) (Ch07.vacuumKet h)) := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · intro m
    exact rho_sea_ne_zero h m.val m.property.1 m.property.2
  · intro m n hmn
    exact rho_sea_orthogonal h m n hmn

/-- Evaluate a linear relation at the sea to transfer excitation independence to actual endomorphisms. -/
lemma rho_linear_independent (h : ℕ) :
    LinearIndependent ℂ (fun m : PositiveMode h => rho h (m.val : ℤ)) := by
  let ev : Operators h →ₗ[ℂ] FockSpace h :=
    { toFun := fun A => A (Ch07.vacuumKet h)
      map_add' := fun A B => rfl
      map_smul' := fun a A => rfl }
  exact LinearIndependent.of_comp ev (rho_sea_linear_independent h)

/-- Covariant transport of a number-conserving density cancels the external step phase.
The remaining root phase depends on transfer m and the chosen translation orientation. -/
lemma rho_transport (h : ℕ) [NeZero (2*h)] (b : Ch06Ext.BoundaryTwist (2*h))
    (m n : ℤ) :
    Ch06Ext.transport (2*h) b n (rho h m) =
      A01.integerCharacter (A01.canonicalRoot (2*h)) (-m) n • rho h m := by
  let χ (t : ℤ) (S : Ch07.Occupation h) : ℂ :=
    b.step^(-t*(S.card : ℤ)) *
      A01.canonicalRoot (2*h)^(-t*Ch05.occupationEnergy (2*h) S)
  have hn := A01.root_ne_zero (2*h) _ (A01.canonical_root_primitive (2*h))
  have ht (t : ℤ) (S : Ch07.Occupation h) :
      Ch06Ext.translation (2*h) b t (A02.ket S) = χ t S • A02.ket S :=
    Ch06Ext.translation_ket (2*h) b t S
  have hc (S T : Ch07.Occupation h)
      (hT : Ch07.relativeCharge h T = Ch07.relativeCharge h S + 0 ∧
        Ch07.excitationEnergy h T = Ch07.excitationEnergy h S + m) :
      χ n T = A01.integerCharacter (A01.canonicalRoot (2*h)) (-m) n * χ n S := by
    have hcard : T.card = S.card := by
      have := hT.1
      unfold Ch07.relativeCharge at this
      omega
    have henergy : Ch05.occupationEnergy (2*h) T =
        Ch05.occupationEnergy (2*h) S + m := by
      have := hT.2
      unfold Ch07.excitationEnergy Ch07.relativeEnergy at this
      have hcharge : Ch07.relativeCharge h T = Ch07.relativeCharge h S := by simpa using hT.1
      rw [hcharge] at this
      omega
    dsimp [χ, A01.integerCharacter]
    rw [hcard, henergy, mul_add, zpow_add₀ hn]
    rw [show -n*m = -m*n by ring]
    ring
  have hv (S : Ch07.Occupation h) :
      Ch06Ext.translation (2*h) b n (rho h m (A02.ket S)) =
        (A01.integerCharacter (A01.canonicalRoot (2*h)) (-m) n * χ n S) •
          rho h m (A02.ket S) := by
    have hgen (v : FockSpace h)
        (hs : v ∈ A03.coordinateSpace {T | Ch07.relativeCharge h T = Ch07.relativeCharge h S + 0 ∧
          Ch07.excitationEnergy h T = Ch07.excitationEnergy h S + m}) :
        Ch06Ext.translation (2*h) b n v =
          (A01.integerCharacter (A01.canonicalRoot (2*h)) (-m) n * χ n S) • v := by
      induction hs using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨T, hT, rfl⟩ := hx
        rw [ht, hc S T hT]
      | zero => simp
      | add x y _ _ hx hy => simp only [map_add, hx, hy, smul_add]
      | smul a x _ hx => simp only [map_smul, hx, smul_smul]; congr 1; ring
    exact hgen _ (rho_exact_shift h m S)
  have hinv (S : Ch07.Occupation h) : χ (-n) S * χ n S = 1 := by
    dsimp [χ]
    calc
      _ = (b.step^(-(-n)*(S.card : ℤ)) * b.step^(-n*(S.card : ℤ))) *
          (A01.canonicalRoot (2*h)^(-(-n)*Ch05.occupationEnergy (2*h) S) *
           A01.canonicalRoot (2*h)^(-n*Ch05.occupationEnergy (2*h) S)) := by ring
      _ = 1 := by
        rw [← zpow_add₀ (Ch06Ext.twist_step_ne_zero (2*h) b), ← zpow_add₀ hn]
        have he (u : ℤ) : -(-n)*u + -n*u = 0 := by ring
        rw [he, he, zpow_zero, zpow_zero, mul_one]
  rw [Ch06Ext.transport_apply]
  apply A02.end_ext_basis
  intro S
  simp only [Module.End.mul_apply, ht, map_smul, hv, LinearMap.smul_apply, smul_smul]
  rw [show χ (-n) S * (A01.integerCharacter (A01.canonicalRoot (2*h)) (-m) n * χ n S) =
      A01.integerCharacter (A01.canonicalRoot (2*h)) (-m) n * (χ (-n) S * χ n S) by ring,
      hinv, mul_one]


end Bosonize.Ch09
