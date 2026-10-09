# CH06 extension companion — boundary holonomy and ring transport

Status (2026-10-09): **Phase A complete; unlocked and unproved, awaiting interface review.** Baseline: `9734230`. The extension contains 29 complete data declarations and 72 one-sorry theorem stubs. It imports frozen CH06 and is exposed by `BosonizeStubs`; no existing Core or approved interface is changed.

## Source reconciliation and scope

The user's request authorizes a separate `ch06_ext` module. Adopt the corrected contracts in [the boundary issue review](../../../note/issue_twisted_boundary_conditions_2026-10-09.md), the actual frozen CH01/A01/CH05/CH06 carriers, and the repository formalizer skill. Read the current [CH06 note](../../../notes/md/ch06_lattice_AQFT_net.md), [TOC](../../../notes/md/TOC.md) and [appendix index](../../../notes/appendices/README.md). Their progress summaries can be stale; compiler sources and locks establish implemented status. The issue review reconciles the user's proposed CH01/A05/CH14 twist sections with vDS and the implemented Fourier convention. Preserve the locally edited source notes; this draft does not validate every statement in those notes.

Graded exchange is distinct from spatial holonomy. The extension covers every external scalar U(1) boundary phase on a positive-length ring through a chosen uniform per-site phase. General non-Abelian transport, arbitrary link gauges and a Jordan–Wigner spin-model equivalence are outside this interface. Arbitrary real offsets are allowed, including irrational ones; ℂ is the implemented scalar carrier. No fractional power of a primitive root or unspecified complex-power branch is introduced.

## Parameters, carriers and implicit dependencies

`BoundaryTwist L` stores a complex `step` r and an actual norm-one certificate. `holonomy L b=r^L` is derived. `angleTwist L β` constructs r=exp(2πiβ/L) with a library-proved certificate; no theorem stub is consumed by data. `angle_twist_surjective` and `holonomy_surjective` are proposed coverage obligations for L>0. Real β records a physical momentum offset; holonomy alone does not select its lift. The periodic object has r=1; centered APBC uses β=-1/2 so the existing band (-h,h] becomes physical half-integers (-h-1/2,h-1/2].

The integer mode index, quotient lattice and finite Fock carrier are reused. The twist is explicit in fields, characters, translations, transport and zero modes. Downstream code can bind `variable {b : Ch06Ext.BoundaryTwist L}` and make b an implicit function argument; Lean still records that dependency. No global typeclass chooses an invisible twist. Equal holonomy does not mean equal step or equal definitions. Root ratios have a proposed periodicity lemma; no unsupported unitary equivalence of finite kinetic spectra is asserted.

Most scalar/operator review contracts are drafted in the common positive-ring context `(L : ℕ) [NeZero L]`. Data also elaborate for L=0 where their underlying carriers exist, but no ring or holonomy coverage interpretation is assigned there. The excitation-energy cancellation explicitly uses L=2*h, h>0, and the same reference sea.

## Lifted fields, Fourier kernels and locality

Define c_b(n)=r^n c_0([n]) on ℤ. Creation uses the conjugate phase; its equality to the actual Hilbert adjoint is a stub. Site fields use x.val as a selected fundamental-domain section. A nontrivial holonomy field cannot be a representative-independent scalar-valued function on ZMod L; `quotient_descent_iff` includes a genuine nonzero annihilator witness to detect this obstruction.

`windingNumber n=n/L` uses integer Euclidean division, including negative n. `seamPhase` is τ to that winding power. The decomposition and lifted-to-site relation explain every wrap, and `site_transport` retains the seam factor for arbitrary integer shifts. Winding laws cover multiple laps in either direction.

The Fourier kernel is r^n ζ^(kn), using the frozen positive Fourier convention. Orthogonality and inverse-transform statements are exact finite sums. Site CAR is canonical; lifted mixed CAR retains r^(n-m) when the residues coincide. Same-species density is the actual untwisted position number. Local algebras and parity subspaces are constructed from the twisted site fields, with equality to frozen CH06 as proof obligations. Scalar cancellation explains reuse of graded locality; locality itself does not encode transport.

## Transport, holonomy and zero modes

On the actual momentum occupation ket δ_S, translation by m is defined as

    T_b(m) δ_S = r^(-m #S) ζ^(-m Σk∈S k) δ_S.

The sign is fixed by positive-kernel annihilator covariance. Define operator transport as T_b(m) A T_b(-m) by complete linear-map data, then propose composition, actual-adjoint, unitarity, star-preserving algebra-automorphism existence and field covariance contracts. This order avoids defining an automorphism using an unproved certificate. Region covariance includes the graded subspaces; number, periodic reference Hamiltonian and parity are preserved.

A full lap is the charge gauge τ^(-#S), so its conjugation acts on an annihilator by τ. At APBC the full-lap operator is occupation parity. Holonomy detection compares this action on nonzero fields. The record stores a transport trivialization rather than merely the unchanged local algebra.

`zeroMode` is a concrete diagonal source-sector phase r^n ζ^(n(#S-referenceCharge)). Basis action, monodromy, unitarity and creator/annihilator ordering factors are stubs. Later Klein maps must use the same b, orientation and source charge. This is neither an implemented Klein map nor a proof of a finite vertex equality. Matching holonomy remains necessary but insufficient for the conditional CH14 criterion.

`jwHolonomy particles=-(-1)^particles` and `jwSectorTwist` provide the separate parity-sector dictionary: even occupations choose APBC, odd occupations periodic. The parity-flip stub makes sector changes visible. They do not assert that a fixed-flux field is already a Jordan–Wigner spin-chain field; odd operators connecting source/target sectors need separately typed intertwiners and a spin Hamiltonian/string convention.

## Physical energy and downstream plan

Physical labels k+β and occupation energies are real-valued. With the same sea, relative energy shifts by β times relative charge. The candidate charge polynomial is t_β(N)=N(N+1)/2+βN. Subtracting it cancels β from excitation energy, with APBC t=N²/2. No nonnegative/minimal-ground claim is built into these definitions; proving those interpretations uses the reviewed CH07 ground and admissibility contracts. Arbitrary dispersion, an alternative sea, or different species twists need their own bridge.

A03 coordinate calculus can stay generic. CH07's proposed integer excitation data can stay as a reference model after this real-energy bridge is proved; its integer triangular charge term must not be called the physical APBC energy. Uniform twist does not remove finite-band edge or Umklapp obligations.

Proposed Phase B order:

1. Unit phases, root/angle coverage, integer winding, orthogonality and inverse Fourier transform.
2. Actual adjoints, winding, nonzero-action/descent and site/lift CAR.
3. Density cancellation, local algebra/grade identification and inherited graded locality.
4. Translation basis action, group law/unitarity, transport automorphism and seam/region covariance; full-lap gauge and APBC parity.
5. Zero-mode ordering and monodromy; the standalone JW parity dictionary.
6. Real physical-energy bridge, then reuse it when proving the already drafted A03/CH07 budgets.

For CH09–CH12, establish twist cancellation for the specified same-species bilinears and fixed-charge excitation budgets. For CH13–CH14/A05, retain a species-indexed family of b and explicitly typed sector transitions. Cross-species bilinears with different twists do not automatically have trivial holonomy. For CH15 onward, separate periodic oscillator data from zero-mode winding, chirality signs, physical charge-energy terms and parameter-dependent observables. Each later definition must retain the necessary parameters; phase independence is a theorem where phases actually cancel, not a global assumption.

## Validation and review boundary

Both library builds pass. Native Lean MCP diagnostics complete with success=true, partial=false, 72 sorry-category warnings, no other diagnostics and no failed dependencies. Fresh axiom output shows all 29 data declarations use only standard axioms or none; every one of the 72 proposed lemmas uses sorryAx. A native goal inspection also returned successfully on a stub; a placeholder can report complete at its endpoint, which is not proof evidence.

All 69 guard regression tests pass. Against `9734230`, non-strict verification preserves all 271 statements/225 frozen commands and all eight complete Core sources. Strict verification intentionally rejects exactly Ch06Ext and the existing unlocked A03/CH07 drafts. No freeze manifest or Core aggregator is changed. Full strict CI is not reported as passing. One primary formalizer performed this Phase A with the repository skill; no subagents were dispatched.

Review the exact source below before locking and Phase B. Source-note corrections from the issue review and the spin-sector model remain separate obligations. The boundary issue is not marked resolved by a draft with placeholders.

## Reviewed source provenance

| Source | SHA-256 |
| --- | --- |
| `note/issue_twisted_boundary_conditions_2026-10-09.md` | `238aceca9228d6576e3912dca63bf72cf531869727f42f05c3f574beb0c6ffe1` |
| `notes/md/ch06_lattice_AQFT_net.md` | `4971a838dbb9255219d9e2b9e1d2039d0865111c6797ba39a86e62d966c39a91` |
| `notes/md/TOC.md` | `5ea6b32bdecf8f9c65a345dc12356ff767b176c0b131e32acdb836778b054977` |
| `notes/appendices/README.md` | `ce871fab4a58ecb41a2b99d4ad4b055bb55e400753249fa88edde45fd15ebcd9` |
| `Bosonize/Core/Ch06LocalNet.lean` | `a60c83172eb262f26c73de11e681dd0da373713328edfa789ad7f0486427094f` |
| `Bosonize/Core/Ch05Fermions.lean` | `a19fed9d032daaa60df6bda4980b7470f10dd3e7333a63aec369a41e75c4dd81` |
| `.agents/skills/formalizer/SKILL.md` | `b65c51851fadb8cd5469c25bfaf34414a074b59e8f89fc7a6b2097969c789aaa` |

## Fresh data and stub axiom output

```text
'Bosonize.Ch06Ext.BoundaryTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.angleTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.periodicTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.antiperiodicTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.holonomy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.liftPhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.sameHolonomy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.annihilation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.creation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.siteAnnihilation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.siteCreation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.density' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.twistedCharacter' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.localGenerators' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.localAlgebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.localPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.translation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.gauge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.windingNumber' does not depend on any axioms
'Bosonize.Ch06Ext.seamPhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.shiftRegion' depends on axioms: [propext, Quot.sound]
'Bosonize.Ch06Ext.zeroMode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.jwHolonomy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.jwSectorTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.physicalMomentum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.physicalOccupationEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.physicalRelativeEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.physicalGroundEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.twist_step_ne_zero' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.holonomy_norm' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.lift_phase_norm' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.lift_phase_add' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.lift_phase_winding' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.angle_holonomy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.angle_twist_surjective' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.holonomy_surjective' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.periodic_holonomy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.antiperiodic_holonomy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.angle_integer_holonomy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.angle_root_shift' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.winding_decomposition' depends on axioms: [propext, sorryAx, Quot.sound]
'Bosonize.Ch06Ext.seam_phase_winding' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.twisted_character_orthogonality' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.twisted_fourier_inverse' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.annihilation_fourier' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.creation_adjoint' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.annihilation_winding' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.creation_winding' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.lift_site_relation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.periodic_field' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.antiperiodic_field' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.annihilation_ne_zero' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.quotient_descent_iff' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.site_annihilation_car' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.site_creation_car' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.site_mixed_car' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.lifted_mixed_car' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.density_untwisted' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.density_periodic' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.local_algebra_eq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.local_part_eq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.graded_locality' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.translation_ket' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.translation_zero' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.translation_add' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.translation_adjoint' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.translation_unitary' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.transport_apply' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.transport_add' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.transport_star' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.transport_automorphism_exists' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.transport_annihilation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.transport_creation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.site_transport' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.seam_transport' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.local_transport' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.local_part_transport' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.translation_preserves_number' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.translation_preserves_hamiltonian' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.translation_preserves_parity' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.full_ring_translation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.translation_power' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.apbc_full_ring_parity' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.holonomy_acts_on_field' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.holonomy_detected_iff' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.change_trivialization_field' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.trivialization_ratio_periodic' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.zero_mode_ket' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.zero_mode_winding' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.zero_mode_unitary' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.zero_mode_creation_order' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.zero_mode_annihilation_order' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.jw_even' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.jw_odd' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.jw_sector_holonomy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.jw_parity_flip' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.physical_energy_shift' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.physical_relative_shift' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.excitation_twist_cancel' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch06Ext.apbc_ground_energy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## Exact Lean source snapshot

Module SHA-256: `5c9542da13b6c00f0d9959b5a6ce5a3587902206b690760c888d6f7f9b30e13e`. The block below matches the source byte-for-byte.

```lean
module

public import Bosonize.Core.Ch06LocalNet
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# CH06 extension: scalar boundary holonomy and covariant ring transport
Phase A: complete data and one-sorry review contracts.
External scalar twists are independent of fermionic grading. Integer lifts expose the seam.
-/

@[expose] public section

namespace Bosonize.Ch06Ext

open scoped BigOperators Classical

/-- A chosen unit per-site phase, including a choice of root/trivialization at length L. -/
structure BoundaryTwist (L : ℕ) where
  step : ℂ
  norm_step : ‖step‖ = 1

/-- All external offset angles are allowed; β is measured in momentum-label units. -/
noncomputable def angleTwist (L : ℕ) (β : ℝ) : BoundaryTwist L :=
  ⟨Complex.exp (((2*Real.pi*β/(L : ℝ) : ℝ) : ℂ)*Complex.I),
    Complex.norm_exp_ofReal_mul_I _⟩

def periodicTwist (L : ℕ) : BoundaryTwist L := ⟨1, norm_one⟩

/-- Centered half-integer momenta use β=-1/2 in the existing positive-Nyquist labels. -/
noncomputable def antiperiodicTwist (L : ℕ) : BoundaryTwist L := angleTwist L (-1/2)

def holonomy (L : ℕ) (b : BoundaryTwist L) : ℂ := b.step^L

noncomputable def liftPhase (L : ℕ) (b : BoundaryTwist L) (n : ℤ) : ℂ := b.step^n

/-- A full-period phase does not specify the selected per-site root. -/
def sameHolonomy (L : ℕ) (b c : BoundaryTwist L) : Prop := holonomy L b = holonomy L c

section Fields
variable (L : ℕ) [NeZero L]

/-- Lift to ℤ; this is not asserted to descend to a periodic scalar-valued quotient field. -/
noncomputable def annihilation (b : BoundaryTwist L) (n : ℤ) : Ch05.Operators L :=
  liftPhase L b n • Ch05.positionAnnihilation L (n : Ch01.Lattice L)

noncomputable def creation (b : BoundaryTwist L) (n : ℤ) : Ch05.Operators L :=
  star (liftPhase L b n) • Ch05.positionCreation L (n : Ch01.Lattice L)

noncomputable def siteAnnihilation (b : BoundaryTwist L) (x : Ch01.Lattice L) : Ch05.Operators L :=
  annihilation L b (x.val : ℤ)

noncomputable def siteCreation (b : BoundaryTwist L) (x : Ch01.Lattice L) : Ch05.Operators L :=
  creation L b (x.val : ℤ)

noncomputable def density (b : BoundaryTwist L) (n : ℤ) : Ch05.Operators L :=
  creation L b n * annihilation L b n

/-- The actual kernel, with integer powers and the chosen external per-site phase. -/
noncomputable def twistedCharacter (b : BoundaryTwist L) (k : Ch01.Band L) (n : ℤ) : ℂ :=
  liftPhase L b n * A01.integerCharacter (A01.canonicalRoot L) k.val n

noncomputable def localGenerators (b : BoundaryTwist L) (I : Ch06.Region L) : Set (Ch05.Operators L) :=
  {A | ∃ x ∈ I, A = siteAnnihilation L b x ∨ A = siteCreation L b x}

noncomputable def localAlgebra (b : BoundaryTwist L) (I : Ch06.Region L) : Subalgebra ℂ (Ch05.Operators L) :=
  Algebra.adjoin ℂ (localGenerators L b I)

noncomputable def localPart (b : BoundaryTwist L) (I : Ch06.Region L) (σ : Ch06.Degree) :
    Submodule ℂ (Ch05.Operators L) :=
  (localAlgebra L b I).toSubmodule ⊓
    LinearMap.ker (Ch06.parityMap L - Ch06.degreeSign σ • LinearMap.id)

/-- Translation by m sites. The minus signs ensure positive-kernel annihilator covariance. -/
noncomputable def translation (b : BoundaryTwist L) (m : ℤ) : Ch05.Operators L :=
  A02.extendBasis (fun S =>
    (b.step^(-m*(S.card : ℤ)) *
      A01.canonicalRoot L^(-m*Ch05.occupationEnergy L S)) • A02.ket S)

noncomputable def gauge (u : ℂ) : Ch05.Operators L :=
  A02.extendBasis (fun S => u^(-(S.card : ℤ)) • A02.ket S)

noncomputable def transport (b : BoundaryTwist L) (m : ℤ) :
    Ch05.Operators L →ₗ[ℂ] Ch05.Operators L :=
  (LinearMap.mulRight ℂ (translation L b (-m))).comp
    (LinearMap.mulLeft ℂ (translation L b m))

def windingNumber (n : ℤ) : ℤ := n / (L : ℤ)

noncomputable def seamPhase (b : BoundaryTwist L) (n : ℤ) : ℂ :=
  holonomy L b ^ windingNumber L n

def shiftRegion (m : ℤ) (I : Ch06.Region L) : Ch06.Region L :=
  (fun x : Ch01.Lattice L => x+(m : Ch01.Lattice L)) '' I

/-- Source-sector phase for later Klein/vertex constructions; no field equality is assumed. -/
noncomputable def zeroMode (b : BoundaryTwist L) (n : ℤ) (referenceCharge : ℤ) : Ch05.Operators L :=
  A02.extendBasis (fun S =>
    (liftPhase L b n * A01.canonicalRoot L^(n*((S.card : ℤ)-referenceCharge))) • A02.ket S)

lemma twist_step_ne_zero (b : BoundaryTwist L) : b.step ≠ 0 := by sorry
lemma holonomy_norm (b : BoundaryTwist L) : ‖holonomy L b‖ = 1 := by sorry
lemma lift_phase_norm (b : BoundaryTwist L) (n : ℤ) : ‖liftPhase L b n‖ = 1 := by sorry
lemma lift_phase_add (b : BoundaryTwist L) (n m : ℤ) :
    liftPhase L b (n+m) = liftPhase L b n * liftPhase L b m := by sorry
lemma lift_phase_winding (b : BoundaryTwist L) (n w : ℤ) :
    liftPhase L b (n+w*(L : ℤ)) = holonomy L b^w * liftPhase L b n := by sorry
lemma angle_holonomy (β : ℝ) :
    holonomy L (angleTwist L β) = Complex.exp (((2*Real.pi*β : ℝ) : ℂ)*Complex.I) := by sorry
lemma angle_twist_surjective (b : BoundaryTwist L) : ∃ β : ℝ, angleTwist L β = b := by sorry
lemma holonomy_surjective (u : ℂ) (hu : ‖u‖ = 1) :
    ∃ b : BoundaryTwist L, holonomy L b = u := by sorry
lemma periodic_holonomy : holonomy L (periodicTwist L) = 1 := by sorry
lemma antiperiodic_holonomy : holonomy L (antiperiodicTwist L) = -1 := by sorry
lemma angle_integer_holonomy (β : ℝ) (z : ℤ) :
    sameHolonomy L (angleTwist L (β+(z : ℝ))) (angleTwist L β) := by sorry
lemma angle_root_shift (β : ℝ) :
    (angleTwist L (β+1)).step = (angleTwist L β).step * A01.canonicalRoot L := by sorry

lemma winding_decomposition (n : ℤ) :
    n = (((n : Ch01.Lattice L).val : ℕ) : ℤ)+windingNumber L n*(L : ℤ) := by sorry
lemma seam_phase_winding (b : BoundaryTwist L) (n w : ℤ) :
    seamPhase L b (n+w*(L : ℤ)) = holonomy L b^w*seamPhase L b n := by sorry
lemma twisted_character_orthogonality (b : BoundaryTwist L) (k p : Ch01.Band L) :
    (∑ x : Ch01.Lattice L,
      star (twistedCharacter L b k (x.val : ℤ))*twistedCharacter L b p (x.val : ℤ)) =
      if k=p then (L : ℂ) else 0 := by sorry
lemma twisted_fourier_inverse (b : BoundaryTwist L) (k : Ch01.Band L) :
    Ch05.momentumAnnihilation L k = (A01.normalization L : ℂ) •
      ∑ x : Ch01.Lattice L, star (twistedCharacter L b k (x.val : ℤ)) •
        siteAnnihilation L b x := by sorry

lemma annihilation_fourier (b : BoundaryTwist L) (n : ℤ) :
    annihilation L b n = (A01.normalization L : ℂ) •
      ∑ k : Ch01.Band L, twistedCharacter L b k n • Ch05.momentumAnnihilation L k := by sorry
lemma creation_adjoint (b : BoundaryTwist L) (n : ℤ) :
    creation L b n = LinearMap.adjoint (annihilation L b n) := by sorry
lemma annihilation_winding (b : BoundaryTwist L) (n w : ℤ) :
    annihilation L b (n+w*(L : ℤ)) = holonomy L b^w • annihilation L b n := by sorry
lemma creation_winding (b : BoundaryTwist L) (n w : ℤ) :
    creation L b (n+w*(L : ℤ)) = star (holonomy L b^w) • creation L b n := by sorry
lemma lift_site_relation (b : BoundaryTwist L) (n : ℤ) :
    annihilation L b n = seamPhase L b n • siteAnnihilation L b (n : Ch01.Lattice L) := by sorry
lemma periodic_field (n : ℤ) :
    annihilation L (periodicTwist L) n = Ch05.positionAnnihilation L (n : Ch01.Lattice L) := by sorry
lemma antiperiodic_field (n : ℤ) :
    annihilation L (antiperiodicTwist L) (n+(L : ℤ)) = -annihilation L (antiperiodicTwist L) n := by sorry
lemma annihilation_ne_zero (b : BoundaryTwist L) (n : ℤ) : annihilation L b n ≠ 0 := by sorry
lemma quotient_descent_iff (b : BoundaryTwist L) :
    (∃ f : Ch01.Lattice L → Ch05.Operators L, ∀ n : ℤ, annihilation L b n = f (n : Ch01.Lattice L)) ↔
      holonomy L b = 1 := by sorry
lemma site_annihilation_car (b : BoundaryTwist L) (x y : Ch01.Lattice L) :
    A02.anticommutator (siteAnnihilation L b x) (siteAnnihilation L b y) = 0 := by sorry
lemma site_creation_car (b : BoundaryTwist L) (x y : Ch01.Lattice L) :
    A02.anticommutator (siteCreation L b x) (siteCreation L b y) = 0 := by sorry
lemma site_mixed_car (b : BoundaryTwist L) (x y : Ch01.Lattice L) :
    A02.anticommutator (siteAnnihilation L b x) (siteCreation L b y) =
      (if x=y then (1 : ℂ) else 0) • (1 : Ch05.Operators L) := by sorry
lemma lifted_mixed_car (b : BoundaryTwist L) (n m : ℤ) :
    A02.anticommutator (annihilation L b n) (creation L b m) =
      (if (n : Ch01.Lattice L)=(m : Ch01.Lattice L) then liftPhase L b (n-m) else 0) •
        (1 : Ch05.Operators L) := by sorry
lemma density_untwisted (b : BoundaryTwist L) (n : ℤ) :
    density L b n = Ch05.positionNumber L (n : Ch01.Lattice L) := by sorry
lemma density_periodic (b : BoundaryTwist L) (n : ℤ) : density L b (n+(L : ℤ)) = density L b n := by sorry
lemma local_algebra_eq (b : BoundaryTwist L) (I : Ch06.Region L) : localAlgebra L b I = Ch06.localAlgebra L I := by sorry
lemma local_part_eq (b : BoundaryTwist L) (I : Ch06.Region L) (σ : Ch06.Degree) :
    localPart L b I σ = Ch06.localPart L I σ := by sorry
lemma graded_locality (b : BoundaryTwist L) (I J : Ch06.Region L) (hIJ : Disjoint I J)
    (σ τ : Ch06.Degree) (A B : Ch05.Operators L)
    (hA : A ∈ localPart L b I σ) (hB : B ∈ localPart L b J τ) :
    A*B = (-1 : ℂ)^(σ.val*τ.val) • (B*A) := by sorry

lemma translation_ket (b : BoundaryTwist L) (m : ℤ) (S : Ch06.Occupation L) :
    translation L b m (A02.ket S) =
      (b.step^(-m*(S.card : ℤ))*A01.canonicalRoot L^(-m*Ch05.occupationEnergy L S)) • A02.ket S := by sorry
lemma translation_zero (b : BoundaryTwist L) : translation L b 0 = 1 := by sorry
lemma translation_add (b : BoundaryTwist L) (m n : ℤ) :
    translation L b (m+n) = translation L b m * translation L b n := by sorry
lemma translation_adjoint (b : BoundaryTwist L) (m : ℤ) :
    LinearMap.adjoint (translation L b m) = translation L b (-m) := by sorry
lemma translation_unitary (b : BoundaryTwist L) (m : ℤ) :
    translation L b m * LinearMap.adjoint (translation L b m) = 1 ∧
      LinearMap.adjoint (translation L b m) * translation L b m = 1 := by sorry
lemma transport_apply (b : BoundaryTwist L) (m : ℤ) (A : Ch05.Operators L) :
    transport L b m A = translation L b m*A*translation L b (-m) := by sorry
lemma transport_add (b : BoundaryTwist L) (m n : ℤ) (A : Ch05.Operators L) :
    transport L b (m+n) A = transport L b m (transport L b n A) := by sorry
lemma transport_star (b : BoundaryTwist L) (m : ℤ) (A : Ch05.Operators L) :
    transport L b m (LinearMap.adjoint A) = LinearMap.adjoint (transport L b m A) := by sorry
lemma transport_automorphism_exists (b : BoundaryTwist L) (m : ℤ) :
    ∃ f : Ch05.Operators L ≃ₐ[ℂ] Ch05.Operators L,
      (∀ A, f A = transport L b m A) ∧
      ∀ A, f (LinearMap.adjoint A) = LinearMap.adjoint (f A) := by sorry
lemma transport_annihilation (b : BoundaryTwist L) (m n : ℤ) :
    transport L b m (annihilation L b n) = annihilation L b (n+m) := by sorry
lemma transport_creation (b : BoundaryTwist L) (m n : ℤ) :
    transport L b m (creation L b n) = creation L b (n+m) := by sorry
lemma site_transport (b : BoundaryTwist L) (m : ℤ) (x : Ch01.Lattice L) :
    transport L b m (siteAnnihilation L b x) =
      seamPhase L b ((x.val : ℤ)+m) • siteAnnihilation L b (x+(m : Ch01.Lattice L)) := by sorry
lemma seam_transport (b : BoundaryTwist L) :
    transport L b 1 (annihilation L b ((L : ℤ)-1)) = holonomy L b • annihilation L b 0 := by sorry
lemma local_transport (b : BoundaryTwist L) (m : ℤ) (I : Ch06.Region L) :
    ∀ A, A ∈ localAlgebra L b I ↔ transport L b m A ∈ localAlgebra L b (shiftRegion L m I) := by sorry
lemma local_part_transport (b : BoundaryTwist L) (m : ℤ) (I : Ch06.Region L) (σ : Ch06.Degree) :
    ∀ A, A ∈ localPart L b I σ ↔ transport L b m A ∈ localPart L b (shiftRegion L m I) σ := by sorry
lemma translation_preserves_number (b : BoundaryTwist L) (m : ℤ) :
    transport L b m (Ch05.totalNumber L) = Ch05.totalNumber L := by sorry
lemma translation_preserves_hamiltonian (b : BoundaryTwist L) (m : ℤ) :
    transport L b m (Ch05.bareHamiltonian L) = Ch05.bareHamiltonian L := by sorry
lemma translation_preserves_parity (b : BoundaryTwist L) (m : ℤ) :
    transport L b m (Ch06.parityOperator L) = Ch06.parityOperator L := by sorry
lemma full_ring_translation (b : BoundaryTwist L) :
    translation L b (L : ℤ) = gauge L (holonomy L b) := by sorry
lemma translation_power (b : BoundaryTwist L) (m : ℕ) :
    translation L b (m : ℤ) = translation L b 1 ^ m := by sorry
lemma apbc_full_ring_parity :
    translation L (antiperiodicTwist L) (L : ℤ) = Ch06.parityOperator L := by sorry
lemma holonomy_acts_on_field (b : BoundaryTwist L) (n : ℤ) :
    transport L b (L : ℤ) (annihilation L b n) = holonomy L b • annihilation L b n := by sorry
lemma holonomy_detected_iff (b c : BoundaryTwist L) :
    (∀ n : ℤ, transport L b (L : ℤ) (annihilation L b n) =
      holonomy L c • annihilation L b n) ↔ sameHolonomy L b c := by sorry
lemma change_trivialization_field (b c : BoundaryTwist L) (n : ℤ) :
    annihilation L c n = (c.step/b.step)^n • annihilation L b n := by sorry
lemma trivialization_ratio_periodic (b c : BoundaryTwist L) (hbc : sameHolonomy L b c) (n : ℤ) :
    (c.step/b.step)^(n+(L : ℤ)) = (c.step/b.step)^n := by sorry
lemma zero_mode_ket (b : BoundaryTwist L) (n referenceCharge : ℤ) (S : Ch06.Occupation L) :
    zeroMode L b n referenceCharge (A02.ket S) =
      (liftPhase L b n*A01.canonicalRoot L^(n*((S.card : ℤ)-referenceCharge))) • A02.ket S := by sorry
lemma zero_mode_winding (b : BoundaryTwist L) (n referenceCharge w : ℤ) :
    zeroMode L b (n+w*(L : ℤ)) referenceCharge = holonomy L b^w • zeroMode L b n referenceCharge := by sorry
lemma zero_mode_unitary (b : BoundaryTwist L) (n referenceCharge : ℤ) :
    LinearMap.adjoint (zeroMode L b n referenceCharge)*zeroMode L b n referenceCharge = 1 := by sorry
lemma zero_mode_creation_order (b : BoundaryTwist L) (n referenceCharge : ℤ) (k : Ch01.Band L) :
    zeroMode L b n referenceCharge*Ch05.momentumCreation L k =
      A01.canonicalRoot L^n • (Ch05.momentumCreation L k*zeroMode L b n referenceCharge) := by sorry
lemma zero_mode_annihilation_order (b : BoundaryTwist L) (n referenceCharge : ℤ) (k : Ch01.Band L) :
    zeroMode L b n referenceCharge*Ch05.momentumAnnihilation L k =
      A01.canonicalRoot L^(-n) • (Ch05.momentumAnnihilation L k*zeroMode L b n referenceCharge) := by sorry

end Fields

/-- A separate source-sector boundary dictionary; not a fixed-flux field identity. -/
noncomputable def jwHolonomy (particles : ℤ) : ℂ := -((-1 : ℂ)^particles)

noncomputable def jwSectorTwist (L : ℕ) (particles : ℤ) : BoundaryTwist L :=
  if Even particles then antiperiodicTwist L else periodicTwist L

lemma jw_even (particles : ℤ) (hp : Even particles) : jwHolonomy particles = -1 := by sorry
lemma jw_odd (particles : ℤ) (hp : Odd particles) : jwHolonomy particles = 1 := by sorry
lemma jw_sector_holonomy (L : ℕ) [NeZero L] (particles : ℤ) :
    holonomy L (jwSectorTwist L particles) = jwHolonomy particles := by sorry
lemma jw_parity_flip (particles : ℤ) : jwHolonomy (particles-1) = -jwHolonomy particles := by sorry

/-- Physical linear-dispersion labels require an offset, not merely its boundary phase. -/
def physicalMomentum (L : ℕ) (β : ℝ) (k : Ch01.Band L) : ℝ := (k.val : ℝ)+β

def physicalOccupationEnergy (L : ℕ) (β : ℝ) (S : Ch06.Occupation L) : ℝ :=
  ∑ k ∈ S, physicalMomentum L β k

def physicalRelativeEnergy (L : ℕ) (β : ℝ) (S : Ch06.Occupation L) : ℝ :=
  physicalOccupationEnergy L β S - physicalOccupationEnergy L β (Ch05.seaConfiguration L)

noncomputable def physicalGroundEnergy (β : ℝ) (N : ℤ) : ℝ := (N : ℝ)*((N : ℝ)+1)/2+β*(N : ℝ)

lemma physical_energy_shift (L : ℕ) (β : ℝ) (S : Ch06.Occupation L) :
    physicalOccupationEnergy L β S = (Ch05.occupationEnergy L S : ℝ)+β*(S.card : ℝ) := by sorry
lemma physical_relative_shift (L : ℕ) (β : ℝ) (S : Ch06.Occupation L) :
    physicalRelativeEnergy L β S =
      ((Ch05.occupationEnergy L S-Ch05.seaEnergy L : ℤ) : ℝ)+
      β*((S.card : ℝ)-((Ch05.seaConfiguration L).card : ℝ)) := by sorry
lemma excitation_twist_cancel (h : ℕ) (hh : 0 < h) (β : ℝ) (S : Ch06.Occupation (2*h)) :
    physicalRelativeEnergy (2*h) β S-physicalGroundEnergy β ((S.card : ℤ)-(h : ℤ)) =
      ((Ch05.occupationEnergy (2*h) S-Ch05.seaEnergy (2*h) : ℤ) : ℝ)-
        physicalGroundEnergy 0 ((S.card : ℤ)-(h : ℤ)) := by sorry
lemma apbc_ground_energy (N : ℤ) : physicalGroundEnergy (-1/2) N = (N : ℝ)^2/2 := by sorry

end Bosonize.Ch06Ext
```
