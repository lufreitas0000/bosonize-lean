module

public import Bosonize.Core.Ch13KleinFactors
public import BosonizeStubs.A05FiniteExponentials

/-!
# CH14: finite phase data and the conditional cyclic field criterion
This file keeps actual finite CAR fields and explicit external boundary twists.
Its Taylor candidate is a polynomial; no unproved nilpotency or unconditional
field–vertex identity is installed as data. Composition acts right to left.
-/
@[expose] public section
namespace Bosonize.Ch14
open scoped BigOperators Classical

section Cyclic
variable {R V W I : Type*} [Semiring R] [AddCommGroup V] [AddCommGroup W]
  [Module R V] [Module R W]

/-- A creator list is written in composition order: the rightmost creator acts first.
The empty word is the identity, so its orbit contains the full ground vector. -/
def creatorWord (G : I → Module.End R V) (is : List I) : Module.End R V :=
  (is.map G).prod

/-- The cyclic submodule is the span of all complete creator-word images of v₀.
No linear independence or chosen partition parametrization is assumed. -/
def cyclicSpan (G : I → Module.End R V) (v₀ : V) : Submodule R V :=
  Submodule.span R (Set.range (fun is : List I => creatorWord G is v₀))

/-- Common residual terms cancel even when nonzero. The ground hypothesis is
an equality of entire vectors, never merely one matrix coefficient. -/
theorem cyclic_common_residual (G : I → Module.End R V) (T : I → Module.End R W)
    (A B : V →ₗ[R] W) (residual : I → V →ₗ[R] W) (v₀ : V)
    (hcyclic : cyclicSpan G v₀ = ⊤) (hground : A v₀ = B v₀)
    (hA : ∀ i, A.comp (G i) = (T i).comp A + residual i)
    (hB : ∀ i, B.comp (G i) = (T i).comp B + residual i) : A = B := by sorry
end Cyclic

section FiniteCAR
variable {σ : Type*} [Fintype σ] [LinearOrder σ]

/-- Preserve CH13's lexicographic species/momentum occupation order. -/
noncomputable local instance localModeLinearOrder (h : ℕ) : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
/-- The strict comparison must use that same lexicographic order. -/
noncomputable local instance localModeLT (h : ℕ) : LT (A05.Mode σ h) := (A05.speciesOrder h).toLT
/-- The weak comparison must use that same lexicographic order. -/
noncomputable local instance localModeLE (h : ℕ) : LE (A05.Mode σ h) := (A05.speciesOrder h).toLE
/-- Finset removal uses the same checked mode equality as the CAR definitions. -/
noncomputable local instance localModeDecidableEq (h : ℕ) : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq

/-- Exact charge and total-excitation occupation predicate, with the original
integer grading. External twist does not change this same-sea excitation label. -/
def budgetSet (h : ℕ) (Ns : σ → ℤ) (K : ℕ) : Set (A05.Occupation σ h) :=
  {S | (∀ ν, Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) = Ns ν) ∧
    Ch07.totalExcitation h S ≤ (K : ℤ)}

/-- Orthogonal coordinate projector onto the actual joint total-energy budget. -/
noncomputable def projection (h : ℕ) (Ns : σ → ℤ) (K : ℕ) : A05.Operators σ h :=
  A03.coordinateProjection (budgetSet h Ns K)

/-- Project an ambient map into the target and restrict its source. Membership
is certified by Core's projector range theorem, independently of chapter stubs. -/
noncomputable def projectedMap (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ)
    (A : A05.Operators σ h) : A05.jointBudget h Ns Kin →ₗ[ℂ] A05.jointBudget h Nt Kout :=
  (projection h Nt Kout * A).domRestrict (A05.jointBudget h Ns Kin) |>.codRestrict
    (A05.jointBudget h Nt Kout) (fun v => by
      change projection h Nt Kout (A v.val) ∈ A03.coordinateSpace (budgetSet h Nt Kout)
      rw [← A03.projection_range]
      exact ⟨A v.val, rfl⟩)

/-- The actual Hilbert adjoint reverses the source and target budget carriers.
Explicit carrier parameters avoid relying on elaborator unfolding of subtype End. -/
noncomputable def budgetAdjoint (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ)
    (A : A05.jointBudget h Ns Kin →ₗ[ℂ] A05.jointBudget h Nt Kout) :
    A05.jointBudget h Nt Kout →ₗ[ℂ] A05.jointBudget h Ns Kin :=
  LinearMap.adjoint (𝕜 := ℂ) (E := A05.jointBudget h Ns Kin) (F := A05.jointBudget h Nt Kout) A

/-- The actual occupation ground ket as a source-budget vector. Core membership
uses admissibility and positive half-length; no desired field equality enters data. -/
noncomputable def groundVector (h : ℕ) (hh : 0<h) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (K : ℕ) : A05.jointBudget h Ns K :=
  ⟨A05.groundKet h Ns, A05.ground_mem_budget h hh Ns hN K⟩

/-- Positive mode labels 1,...,M carry the rational coefficient ζ^(mx)/m.
This is the actual lowering phase W⁺; a zero cutoff is permitted as an empty sum. -/
noncomputable def wPlus (h M : ℕ) (ν : σ) (x : ℤ) : A05.Operators σ h :=
  ∑ m ∈ Finset.range M, (A01.integerCharacter (A01.canonicalRoot (2*h)) ((m+1 : ℕ) : ℤ) x /
    (m+1 : ℂ)) • A05.rho h ν (-((m+1 : ℕ) : ℤ))

/-- The minus sign and negative Fourier exponent are both essential:
W⁻ = -Σ ζ^(-mx)ρₘ/m, hence (W⁺)† = -W⁻. -/
noncomputable def wMinus (h M : ℕ) (ν : σ) (x : ℤ) : A05.Operators σ h :=
  -∑ m ∈ Finset.range M, (A01.integerCharacter (A01.canonicalRoot (2*h)) (-((m+1 : ℕ) : ℤ)) x /
    (m+1 : ℂ)) • A05.rho h ν ((m+1 : ℕ) : ℤ)

/-- Ambient compression keeps both coordinate projections; outside the selected
budget this map is zero. Nilpotency is a theorem, not part of its definition. -/
noncomputable def compressedPlus (h M : ℕ) (Ns : σ → ℤ) (K : ℕ) (ν : σ) (x : ℤ) : A05.Operators σ h :=
  projection h Ns K * wPlus h M ν x * projection h Ns K

/-- Actual raising compression retains the right and left budget projections.
Its nilpotency follows from the checked lowering grading and actual adjoint. -/
noncomputable def compressedMinus (h M : ℕ) (Ns : σ → ℤ) (K : ℕ) (ν : σ) (x : ℤ) : A05.Operators σ h :=
  projection h Ns K * wMinus h M ν x * projection h Ns K

/-- Source-sector phase rν^x ζ^(xNν). The external step root is explicit;
integer charge alone contributes no nontrivial full-lap holonomy. -/
noncomputable def zeroScalar (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) : ℂ :=
  Ch06Ext.liftPhase (2*h) (b ν) x * A01.integerCharacter (A01.canonicalRoot (2*h)) (Ns ν) x

/-- On a fixed source sector the zero mode is this scalar times its identity.
The operator must precede the Klein sector shift. -/
noncomputable def zeroMode (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (K : ℕ) : Module.End ℂ (A05.jointBudget h Ns K) :=
  zeroScalar h b Ns ν x • LinearMap.id

/-- Actual lifted physical field between the source and lowered-charge target.
The entire target projection is retained, including occupation-hole losses. -/
noncomputable def physicalMap (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kin Kout : ℕ) :
    A05.jointBudget h Ns Kin →ₗ[ℂ] A05.jointBudget h (Ch13.lowerCharge Ns ν) Kout :=
  projectedMap h Ns (Ch13.lowerCharge Ns ν) Kin Kout (A05.liftedAnnihilation h b ν x)

/-- The ordered finite polynomial candidate: source Z, projected Klein shift,
shifted-input W⁺ Taylor, target cutoff transition, output compressed W⁻ Taylor.
Projection makes every arrow genuinely typed; no identity with the field is assumed. -/
noncomputable def vertexCandidate (h M : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kin Kout : ℕ) :
    A05.jointBudget h Ns Kin →ₗ[ℂ] A05.jointBudget h (Ch13.lowerCharge Ns ν) Kout :=
  let Nt := Ch13.lowerCharge Ns ν
  (A01.normalization (2*h) : ℂ) •
    (A05Exp.finiteTaylor Kout (projectedMap h Nt Nt Kout Kout (wMinus h M ν x))).comp
      ((projectedMap h Nt Nt Kin Kout LinearMap.id).comp
        ((A05Exp.finiteTaylor Kin (projectedMap h Nt Nt Kin Kin (wPlus h M ν x))).comp
          ((projectedMap h Ns Nt Kin Kin (Ch13.kleinKernel h Ns ν Kin)).comp
            (zeroMode h b Ns ν x Kin))))

/-- Projection evaluation exposes the retained target factor, rather than
silently replacing it by an unrestricted ambient operator. -/
lemma projected_map_apply (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ)
    (A : A05.Operators σ h) (v : A05.jointBudget h Ns Kin) :
    (projectedMap h Ns Nt Kin Kout A v : A05.FockSpace σ h) = projection h Nt Kout (A v) := by sorry

/-- The true adjoint reverses the restricted source and target. Both outer
coordinate projections remain visible through the reverse projected map. -/
lemma projected_map_adjoint (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ)
    (A : A05.Operators σ h) :
    budgetAdjoint h Ns Nt Kin Kout (projectedMap h Ns Nt Kin Kout A) =
      projectedMap h Nt Ns Kout Kin (LinearMap.adjoint A) := by sorry

/-- The candidate's adjoint reverses all five actual typed factors. No raising
or lowering factor is commuted through another, and the transition reverses cutoffs. -/
lemma vertex_candidate_adjoint (h M : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kin Kout : ℕ) :
    let Nt := Ch13.lowerCharge Ns ν
    budgetAdjoint h Ns Nt Kin Kout (vertexCandidate h M b Ns ν x Kin Kout) =
      (A01.normalization (2*h) : ℂ) •
        (budgetAdjoint h Ns Ns Kin Kin (zeroMode h b Ns ν x Kin)).comp
          ((budgetAdjoint h Ns Nt Kin Kin (projectedMap h Ns Nt Kin Kin (Ch13.kleinKernel h Ns ν Kin))).comp
            ((budgetAdjoint h Nt Nt Kin Kin (A05Exp.finiteTaylor Kin (projectedMap h Nt Nt Kin Kin (wPlus h M ν x)))).comp
              ((budgetAdjoint h Nt Nt Kin Kout (projectedMap h Nt Nt Kin Kout LinearMap.id)).comp
                (budgetAdjoint h Nt Nt Kout Kout (A05Exp.finiteTaylor Kout (projectedMap h Nt Nt Kout Kout (wMinus h M ν x))))))) := by sorry

/-- These coefficients have no external twist: the density-current Fourier
modes are periodic bilinears. Nonzero ring length is necessary for ζ's order. -/
lemma w_plus_periodic (h M : ℕ) [NeZero (2*h)] (ν : σ) (x w : ℤ) :
    wPlus h M ν (x+w*(2*h : ℕ)) = wPlus h M ν x := by sorry

/-- Raising phase periodicity uses the same integer-lift convention. -/
lemma w_minus_periodic (h M : ℕ) [NeZero (2*h)] (ν : σ) (x w : ℤ) :
    wMinus h M ν (x+w*(2*h : ℕ)) = wMinus h M ν x := by sorry

/-- Actual Hilbert adjoint, including complex conjugation and the minus sign. -/
lemma w_plus_adjoint (h M : ℕ) [NeZero (2*h)] (ν : σ) (x : ℤ) :
    LinearMap.adjoint (wPlus h M ν x) = -wMinus h M ν x := by sorry

/-- The reciprocal adjoint identity retains the same ambient carrier. -/
lemma w_minus_adjoint (h M : ℕ) [NeZero (2*h)] (ν : σ) (x : ℤ) :
    LinearMap.adjoint (wMinus h M ν x) = -wPlus h M ν x := by sorry

/-- Each strictly positive lowering mode decreases excitation by at least one.
After K+1 compressed steps no nonnegative excitation can remain. -/
lemma compressed_plus_nilpotent (h M : ℕ) (hh : 0<h) (Ns : σ → ℤ) (K : ℕ) (ν : σ) (x : ℤ) :
    compressedPlus h M Ns K ν x ^ (K+1) = 0 := by sorry

/-- Adjoint reversal and the minus sign transfer lowering nilpotency to the
actual compressed raising operator, with no finite-dimensionality shortcut. -/
lemma compressed_minus_nilpotent (h M : ℕ) (hh : 0<h) (Ns : σ → ℤ) (K : ℕ) (ν : σ) (x : ℤ) :
    compressedMinus h M Ns K ν x ^ (K+1) = 0 := by sorry

/-- On the actual subtype carrier, projected lowering has the same degree bound. -/
lemma projected_plus_nilpotent (h M : ℕ) (hh : 0<h) (Ns : σ → ℤ) (K : ℕ) (ν : σ) (x : ℤ) :
    projectedMap h Ns Ns K K (wPlus h M ν x) ^ (K+1) = 0 := by sorry

/-- On the actual subtype carrier, projected raising has the same degree bound. -/
lemma projected_minus_nilpotent (h M : ℕ) (hh : 0<h) (Ns : σ → ℤ) (K : ℕ) (ν : σ) (x : ℤ) :
    projectedMap h Ns Ns K K (wMinus h M ν x) ^ (K+1) = 0 := by sorry

/-- Both the external lift and the integer-charge Fourier factor have modulus one. -/
lemma zero_scalar_norm (h : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) : ‖zeroScalar h b Ns ν x‖ = 1 := by sorry

/-- Around w laps only the explicitly chosen external holonomy remains. -/
lemma zero_scalar_winding (h : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x w : ℤ) :
    zeroScalar h b Ns ν (x+w*(2*h : ℕ)) = Ch06Ext.holonomy (2*h) (b ν)^w * zeroScalar h b Ns ν x := by sorry

/-- The source zero mode carries the same holonomy as the actual field. -/
lemma zero_mode_winding (h : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x w : ℤ) (K : ℕ) :
    zeroMode h b Ns ν (x+w*(2*h : ℕ)) K =
      Ch06Ext.holonomy (2*h) (b ν)^w • zeroMode h b Ns ν x K := by sorry

/-- The actual source-budget Hilbert adjoint is the inverse unit phase. -/
lemma zero_mode_adjoint (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (K : ℕ) :
    LinearMap.adjoint (𝕜 := ℂ) (E := A05.jointBudget h Ns K) (F := A05.jointBudget h Ns K) (zeroMode h b Ns ν x K) = star (zeroScalar h b Ns ν x) • LinearMap.id := by sorry

/-- A source-budget zero mode is unitary, including both composition orders. -/
lemma zero_mode_unitary (h : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (K : ℕ) :
    LinearMap.adjoint (𝕜 := ℂ) (E := A05.jointBudget h Ns K) (F := A05.jointBudget h Ns K) (zeroMode h b Ns ν x K) * zeroMode h b Ns ν x K = 1 ∧
      zeroMode h b Ns ν x K * LinearMap.adjoint (𝕜 := ℂ) (E := A05.jointBudget h Ns K) (F := A05.jointBudget h Ns K) (zeroMode h b Ns ν x K) = 1 := by sorry

/-- Source-phase evaluation precedes Klein lowering and reproduces the complete
Klein-ground image; this image is still not the full physical field ground image. -/
lemma klein_zero_ground (h : ℕ) (hh : 0<h) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (K : ℕ) (hm : Ch13.pairMargin h K Ns ν) :
    Ch13.kleinKernel h Ns ν K (zeroScalar h b Ns ν x • A05.groundKet h Ns) =
      (zeroScalar h b Ns ν x * Ch13.kleinPhase h Ns ν) • A05.groundKet h (Ch13.lowerCharge Ns ν) := by sorry

/-- Full retained hole-ket expansion for any occupation. The CAR removal sign
uses the lexicographic order and every Fourier momentum remains visible. -/
lemma physical_occupation_expansion (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kout : ℕ) (S : A05.Occupation σ h) :
    projection h (Ch13.lowerCharge Ns ν) Kout (A05.liftedAnnihilation h b ν x (A02.ket S)) =
      (A01.normalization (2*h) : ℂ) •
        ∑ k : Ch01.Band (2*h), if (ν,k) ∈ S then
          (Ch06Ext.twistedCharacter (2*h) (b ν) k x * Ch04.fermionSign (ν,k) S) •
            projection h (Ch13.lowerCharge Ns ν) Kout (A02.ket (S.erase (ν,k))) else 0 := by sorry

/-- Specialize the entire retained hole expansion to the actual source ground.
Deep occupied momenta are retained or removed individually by the target projector. -/
lemma physical_ground_expansion (h : ℕ) (hh : 0<h) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (hN : A05.admissible h Ns) (ν : σ) (x : ℤ) (Kin Kout : ℕ) :
    (physicalMap h b Ns ν x Kin Kout (groundVector h hh Ns hN Kin) : A05.FockSpace σ h) =
      (A01.normalization (2*h) : ℂ) •
        ∑ k : Ch01.Band (2*h), if (ν,k) ∈ A05.groundConfiguration h Ns then
          (Ch06Ext.twistedCharacter (2*h) (b ν) k x * Ch04.fermionSign (ν,k) (A05.groundConfiguration h Ns)) •
            projection h (Ch13.lowerCharge Ns ν) Kout
              (A02.ket ((A05.groundConfiguration h Ns).erase (ν,k))) else 0 := by sorry

/-- Exact ambient recurrence remainder with both boundary excursions retained.
This algebraic identity does not assert either excursion vanishes. -/
lemma projected_recurrence_residual (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ)
    (c rho : A05.Operators σ h) :
    let Pin := projection h Ns Kin
    let Pout := projection h Nt Kout
    (Pout*c*Pin)*(Pin*rho*Pin) - (Pout*rho*Pout)*(Pout*c*Pin) =
      Pout*(c*rho-rho*c)*Pin - Pout*c*(1-Pin)*rho*Pin + Pout*rho*(1-Pout)*c*Pin := by sorry

/-- The physical field between typed budgets has exactly the external winding
phase, irrespective of which holes the target projection retains. -/
lemma physical_map_winding (h : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x w : ℤ) (Kin Kout : ℕ) :
    physicalMap h b Ns ν (x+w*(2*h : ℕ)) Kin Kout =
      Ch06Ext.holonomy (2*h) (b ν)^w • physicalMap h b Ns ν x Kin Kout := by sorry

/-- The candidate carries the identical holonomy through its source zero mode;
the periodic phases and cutoff projections contribute no extra boundary factor. -/
lemma vertex_candidate_winding (h M : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x w : ℤ) (Kin Kout : ℕ) :
    vertexCandidate h M b Ns ν (x+w*(2*h : ℕ)) Kin Kout =
      Ch06Ext.holonomy (2*h) (b ν)^w • vertexCandidate h M b Ns ν x Kin Kout := by sorry

/-- Apply the abstract cyclic criterion to the actual typed field and polynomial
candidate. Full ground equality and common residual recurrences remain independent
physical obligations; numerical margins alone do not prove any of them. -/
theorem field_vertex_of_common_residual (h M : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kin Kout : ℕ)
    {I : Type*} (G : I → Module.End ℂ (A05.jointBudget h Ns Kin))
    (T : I → Module.End ℂ (A05.jointBudget h (Ch13.lowerCharge Ns ν) Kout))
    (residual : I → A05.jointBudget h Ns Kin →ₗ[ℂ] A05.jointBudget h (Ch13.lowerCharge Ns ν) Kout)
    (v₀ : A05.jointBudget h Ns Kin)
    (hcyclic : cyclicSpan G v₀ = ⊤)
    (hground : physicalMap h b Ns ν x Kin Kout v₀ = vertexCandidate h M b Ns ν x Kin Kout v₀)
    (hA : ∀ i, (physicalMap h b Ns ν x Kin Kout).comp (G i) =
      (T i).comp (physicalMap h b Ns ν x Kin Kout) + residual i)
    (hB : ∀ i, (vertexCandidate h M b Ns ν x Kin Kout).comp (G i) =
      (T i).comp (vertexCandidate h M b Ns ν x Kin Kout) + residual i) :
    physicalMap h b Ns ν x Kin Kout = vertexCandidate h M b Ns ν x Kin Kout := by sorry
end FiniteCAR
end Bosonize.Ch14
