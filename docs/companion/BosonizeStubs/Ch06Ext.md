# CH06 extension companion — boundary holonomy and ring transport

Status (2026-10-09): **Phase A complete; unlocked and unproved, awaiting interface review.** Baseline: `9734230`. The extension contains 29 complete data declarations and 72 one-sorry theorem stubs. It imports frozen CH06 and is exposed by `BosonizeStubs`; no existing Core or approved interface is changed.

## Source reconciliation and scope

The user's request authorizes a separate `ch06_ext` module. Adopt the corrected contracts in [the boundary issue review](../../../note/issue_twisted_boundary_conditions_2026-10-09.md), the actual frozen CH01/A01/CH05/CH06 carriers, and the repository formalizer skill. Read the current [CH06 note](../../../notes/md/ch06_lattice_AQFT_net.md), [TOC](../../../notes/md/TOC.md) and [appendix index](../../../notes/appendices/README.md). Their progress summaries can be stale; compiler sources and locks establish implemented status. The issue review reconciles the user's proposed CH01/A05/CH14 twist sections with vDS and the implemented Fourier convention. Preserve the locally edited source notes; this draft does not validate every statement in those notes.

Graded exchange is distinct from spatial holonomy. The extension covers every external scalar U(1) boundary phase on a positive-length ring through a chosen uniform per-site phase. General non-Abelian transport, arbitrary link gauges and a Jordan–Wigner spin-model equivalence are outside this interface. Arbitrary real offsets are allowed, including irrational ones; ℂ is the implemented scalar carrier. No fractional power of a primitive root or unspecified complex-power branch is introduced.

## Parameters, carriers and implicit dependencies

`BoundaryTwist L` stores a complex `step` r and an actual norm-one certificate. `holonomy L b=r^L` is derived. `angleTwist L β` constructs r=exp(2πiβ/L) with a library-proved certificate; no theorem stub is consumed by data. `angle_twist_surjective` and `holonomy_surjective` are proposed coverage obligations for L>0. Real β records a physical momentum offset; holonomy alone does not select its lift. The periodic object has r=1; centered APBC uses β=-1/2 so the existing band (-h,h] becomes physical half-integers (-h-1/2,h-1/2].

The integer mode index, quotient lattice and finite Fock carrier are reused. The twist is explicit in fields, characters, translations, transport and zero modes. Downstream code can bind `variable {b : Ch06Ext.BoundaryTwist L}` and make b an implicit function argument; Lean still records that dependency. No global typeclass chooses an invisible twist. Equal holonomy does not mean equal step or equal definitions. Root ratios have a proposed periodicity lemma; no unsupported unitary equivalence of finite kinetic spectra is asserted.

Most scalar/operator review contracts are drafted in the common positive-ring context `(L : ℕ) [NeZero L]`. Data also elaborate for L=0 where their underlying carriers exist, but no ring or holonomy coverage interpretation is assigned there. The excitation-energy cancellation explicitly uses L=2*h, h>0, and the same reference sea.

## How later chapters select the algebra and operators

The shared carrier stays `Ch05.Operators L`. Retain frozen `Ch06.localAlgebra` and
`Ch06.localPart` for support/grading calculations; use the extension's fields, kernels,
transport and zero modes whenever boundary data matter. After proof, `local_algebra_eq`
and `local_part_eq` transfer between the twisted-generator and frozen presentations.
Using the CH06 algebra does not select periodic transport or erase an operator's twist.

For a uniform angular model choose `b = angleTwist L β` and use the same β in physical
momentum/energy and the same b in every comparison field, transport and zero mode.
A theorem with `(b : BoundaryTwist L)` is universal in b; an implicit `{b : BoundaryTwist L}`
argument hides only its spelling at a call site, not its mathematical dependency.
The general development retains b until an explicit specialization or a proved
cancellation removes it. Independent species will need a family of records.

The Lean module now has expanded documentation before all 29 data declarations and
72 proposed lemmas, plus field-level documentation and a notation/API guide. Comments
change no normalized declarations, theorem statements, definitions or proof bodies.

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

Module SHA-256: `89fd0a834a0824459ddfbd4c29aaadd18f7e1412f7609a25a8c14e84939cae17`. The block below matches the source byte-for-byte.

```lean
module

public import Bosonize.Core.Ch06LocalNet
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# CH06 extension: scalar boundary holonomy and covariant ring transport
Phase A: complete data and one-sorry review contracts.
External scalar twists are independent of fermionic grading. Integer lifts expose the seam.

## Reading the notation and choosing downstream APIs

`b : BoundaryTwist L` is an ordinary parameter, not a global inferred physical choice.
Current definitions take it explicitly. A later section may bind `{b : BoundaryTwist L}`
to produce implicit arguments; Lean still retains b in the resulting declaration's type.
Quantifying a theorem over b states validity for every twist. Independence requires an
identity removing b, such as the proposed density_untwisted or local_algebra_eq bridge.

`step` means the complex phase r per lattice step; `holonomy` means r^L per complete lap.
On complex numbers `star z` is conjugation. Actual operator adjoints use
`LinearMap.adjoint A`. `a • A` is scalar multiplication, whereas `A * B` is composition
with B acting first. The same • notation scales Fock vectors when its right operand is a ket.

All operators live in the existing `Ch05.Operators L`; there is no competing Fock carrier.
Use frozen `Ch06.localAlgebra` / `Ch06.localPart` for local support and grading when
spatial twist is irrelevant. Use `Ch06Ext.annihilation`, `creation`, `twistedCharacter`,
`translation`, `transport` and `zeroMode`, with the same b, for boundary-sensitive work.
The proposed local_algebra_eq and local_part_eq lemmas transfer local statements between
presentations after they are proved. A β-dependent physical-energy model must explicitly
select b=angleTwist L β. Specialize b=periodicTwist L or antiperiodicTwist L only when
the model calls for that sector; the general development can retain b throughout.
All 72 lemmas below remain proposed contracts with sorry placeholders.

-/

@[expose] public section

namespace Bosonize.Ch06Ext

open scoped BigOperators Classical

/--
Boundary data for a ring of length L: a chosen uniform complex phase r per lattice step,
together with its norm-one certificate. The full-ring phase is derived as r^L. Different choices
of r can have the same full-ring phase, so this record retains the chosen transport/Fourier
trivialization. L indexes that choice; positive-length hypotheses enter the ring theorems.
-/
structure BoundaryTwist (L : ℕ) where
  /-- Uniform phase r per lattice step, not the complete-loop phase r^L. -/
  step : ℂ
  /-- Actual unit-modulus certificate; in particular step is nonzero and invertible. -/
  norm_step : ‖step‖ = 1

/--
Construct the step phase r = exp(2πiβ/L) from a real momentum offset β, measured in integer-
label units. Its norm certificate comes from Mathlib rather than a theorem stub. For L>0 the
proposed angle_holonomy lemma gives exp(2πiβ) around the ring. Retain β separately when an
energy or physical momentum depends on its real lift.
-/
noncomputable def angleTwist (L : ℕ) (β : ℝ) : BoundaryTwist L :=
  ⟨Complex.exp (((2*Real.pi*β/(L : ℝ) : ℝ) : ℂ)*Complex.I),
    Complex.norm_exp_ofReal_mul_I _⟩

/--
Choose r=1, so the external phase is trivial at every lattice step and around the ring. This
selects the existing periodic convention exactly; a different root with holonomy one can still
give different position-dependent phases.
-/
def periodicTwist (L : ℕ) : BoundaryTwist L := ⟨1, norm_one⟩

/--
Choose β=-1/2 and hence r=exp(-πi/L). At positive L its full-ring phase is -1. For L=2h this
shifts the retained integer band [-h+1,h] to the centered physical half-integers [-h+1/2,h-1/2];
integer mode indices themselves stay unchanged.
-/
noncomputable def antiperiodicTwist (L : ℕ) : BoundaryTwist L := angleTwist L (-1/2)

/--
The scalar phase τ=r^L acquired by the annihilation field after one positive lap of the ring.
Holonomy records full-loop transport, whereas step records the chosen phase per site. This is
spatial boundary data, distinct from the sign of exchanging two odd operators.
-/
def holonomy (L : ℕ) (b : BoundaryTwist L) : ℂ := b.step^L

/--
The chosen phase r^n at an integer position n. The integer power permits negative positions
without fractional complex powers; norm one makes r nonzero. Positions remain in ℤ here because
a field with nontrivial holonomy cannot descend to an ordinary periodic function on ZMod L.
-/
noncomputable def liftPhase (L : ℕ) (b : BoundaryTwist L) (n : ℤ) : ℂ := b.step^n

/--
Say that two twist records have the same full-ring phase. This compares holonomy only, not
record equality or the selected step root. The proposed change-of-trivialization lemmas explain
the position-dependent ratio between their fields.
-/
def sameHolonomy (L : ℕ) (b c : BoundaryTwist L) : Prop := holonomy L b = holonomy L c

section Fields
variable (L : ℕ) [NeZero L]

/--
The lifted twisted annihilator c_b(n)=r^n • c_0([n]) on the existing finite Fock space. The
argument b explicitly records its twist dependency, and [n] is the residue in ZMod L. The symbol
• denotes complex scalar multiplication of a linear operator: (a • A)(v)=a • A(v). It is
distinct from operator composition A*B.
-/
noncomputable def annihilation (b : BoundaryTwist L) (n : ℤ) : Ch05.Operators L :=
  liftPhase L b n • Ch05.positionAnnihilation L (n : Ch01.Lattice L)

/--
The lifted creator with conjugate scalar phase: star(r^n) • c_0†([n]). Here star acts on ℂ and
means complex conjugation. Hilbert adjoints of operators are written LinearMap.adjoint, and creation_adjoint is the proposed proof that this definition
is the actual adjoint of annihilation.
-/
noncomputable def creation (b : BoundaryTwist L) (n : ℤ) : Ch05.Operators L :=
  star (liftPhase L b n) • Ch05.positionCreation L (n : Ch01.Lattice L)

/--
Evaluate the lifted annihilator on the chosen representative x.val in {0,...,L-1}. This is a
fundamental-domain section on the quotient lattice, not a claim that all integer lifts of x give
the same operator. Winding and seam phases must be retained when transporting beyond the
representatives.
-/
noncomputable def siteAnnihilation (b : BoundaryTwist L) (x : Ch01.Lattice L) : Ch05.Operators L :=
  annihilation L b (x.val : ℤ)

/--
Evaluate the lifted creator on x.val using the same twist and representative convention as
siteAnnihilation. Its scalar is conjugated, so the site mixed-CAR and adjoint contracts have the
correct phase cancellation.
-/
noncomputable def siteCreation (b : BoundaryTwist L) (x : Ch01.Lattice L) : Ch05.Operators L :=
  creation L b (x.val : ℤ)

/--
The ordered same-species product c_b†(n)*c_b(n). Multiplication in the operator algebra is
composition, with the right factor acting first. Both factors use the same b, so the proposed
density_untwisted lemma cancels their conjugate phases; cross-species products with different
twists require separate accounting.
-/
noncomputable def density (b : BoundaryTwist L) (n : ℤ) : Ch05.Operators L :=
  creation L b n * annihilation L b n

/--
The positive-sign Fourier kernel r^n ζ^(k n), with ζ the frozen canonical L-th root and k the
retained integer band label. Its b dependency supplies the external offset; integer powers and
an explicit step root avoid a fractional-power branch. star of this complex kernel is its
conjugate in the inverse transform.
-/
noncomputable def twistedCharacter (b : BoundaryTwist L) (k : Ch01.Band L) (n : ℤ) : ℂ :=
  liftPhase L b n * A01.integerCharacter (A01.canonicalRoot L) k.val n

/--
The twisted site annihilators and creators supported in region I, inside the shared algebra
Ch05.Operators L. Both types of generator are included to support adjoint closure. Region I is a
set of quotient sites; seam information belongs to their transport, not to a second spatial
carrier.
-/
noncomputable def localGenerators (b : BoundaryTwist L) (I : Ch06.Region L) : Set (Ch05.Operators L) :=
  {A | ∃ x ∈ I, A = siteAnnihilation L b x ∨ A = siteCreation L b x}

/--
The unital complex subalgebra generated by the twisted site fields in I. Its definition retains
b even though local_algebra_eq proposes equality to the frozen CH06 algebra for every unit
twist. Later spatial-covariance statements use this presentation; purely local algebra
statements can be transferred through that equality after it is proved.
-/
noncomputable def localAlgebra (b : BoundaryTwist L) (I : Ch06.Region L) : Subalgebra ℂ (Ch05.Operators L) :=
  Algebra.adjoin ℂ (localGenerators L b I)

/--
The parity-σ subspace of the twisted local algebra, using the existing CH06 parity map and
degree sign. The intersection and linear-map kernel keep the odd part a submodule rather than
incorrectly making it a subalgebra. The scalar • on LinearMap.id rescales that map; the grading
sign is separate from spatial holonomy.
-/
noncomputable def localPart (b : BoundaryTwist L) (I : Ch06.Region L) (σ : Ch06.Degree) :
    Submodule ℂ (Ch05.Operators L) :=
  (localAlgebra L b I).toSubmodule ⊓
    LinearMap.ker (Ch06.parityMap L - Ch06.degreeSign σ • LinearMap.id)

/--
Construct translation by m integer steps as a diagonal map on the actual momentum-occupation
basis. On δ_S it multiplies by r^(-m #S) ζ^(-m sum(k∈S) k). The negative exponents match the
positive annihilation Fourier convention. Unitarity and field covariance are proposed lemmas,
not certificates assumed in this definition.
-/
noncomputable def translation (b : BoundaryTwist L) (m : ℤ) : Ch05.Operators L :=
  A02.extendBasis (fun S =>
    (b.step^(-m*(S.card : ℤ)) *
      A01.canonicalRoot L^(-m*Ch05.occupationEnergy L S)) • A02.ket S)

/--
Construct the diagonal charge-gauge map δ_S ↦ u^(-#S) • δ_S for a complex scalar u. When u is
unit modulus this is the full-lap candidate for holonomy u; the definition itself accepts
arbitrary u and does not assert unitarity at u=0. Its negative exponent follows the annihilator
transport convention.
-/
noncomputable def gauge (u : ℂ) : Ch05.Operators L :=
  A02.extendBasis (fun S => u^(-(S.card : ℤ)) • A02.ket S)

/--
The linear map on operators A ↦ T_b(m)*A*T_b(-m), constructed using left and right
multiplication. The carrier remains Ch05.Operators L and composition acts rightmost first.
Translation inverse/unitarity and star-preserving algebra-automorphism properties must be proved
before using this as certified conjugation by a unitary.
-/
noncomputable def transport (b : BoundaryTwist L) (m : ℤ) :
    Ch05.Operators L →ₗ[ℂ] Ch05.Operators L :=
  (LinearMap.mulRight ℂ (translation L b (-m))).comp
    (LinearMap.mulLeft ℂ (translation L b m))

/--
The integer quotient n/L in Euclidean division for positive ring length L. It counts signed laps
relative to the selected representative of [n]; negative n can have negative winding. The
proposed winding_decomposition relates it exactly to ZMod.val, rather than relying on truncating
natural subtraction.
-/
def windingNumber (n : ℤ) : ℤ := n / (L : ℤ)

/--
The phase τ^w for w=windingNumber(n). It restores the holonomy lost when an integer position is
replaced by its selected quotient representative. With b fixed, it records any number of seam
crossings in either direction.
-/
noncomputable def seamPhase (b : BoundaryTwist L) (n : ℤ) : ℂ :=
  holonomy L b ^ windingNumber L n

/--
Translate each quotient site of I by the residue of integer m. The result wraps on the finite
ring and is independent of b as a set. The operators transported between these regions still
depend on b and can acquire seam phases.
-/
def shiftRegion (m : ℤ) (I : Ch06.Region L) : Ch06.Region L :=
  (fun x : Ch01.Lattice L => x+(m : Ch01.Lattice L)) '' I

/--
Construct the source-sector phase r^n ζ^(n(#S-referenceCharge)) on δ_S. The offset
referenceCharge converts total occupation to the intended relative charge, and the same b as the
comparison field supplies its external holonomy. Later Klein/vertex constructions must preserve
source-before-lowering order; this definition does not establish a vertex equality.
-/
noncomputable def zeroMode (b : BoundaryTwist L) (n : ℤ) (referenceCharge : ℤ) : Ch05.Operators L :=
  A02.extendBasis (fun S =>
    (liftPhase L b n * A01.canonicalRoot L^(n*((S.card : ℤ)-referenceCharge))) • A02.ket S)

/--
Proposed consequence of norm_step: the selected step phase cannot vanish. This supplies the
nonzero condition needed for integer negative powers, division by step, and invertible scalar
changes of generators. The lemma remains a Phase A placeholder.
-/
lemma twist_step_ne_zero (b : BoundaryTwist L) : b.step ≠ 0 := by sorry
/--
Proposed norm-one property of the full-loop phase r^L. It permits treating holonomy as scalar
U(1) boundary data and using its conjugate as its inverse. No restriction to rational angles or
periodic/APBC phases is imposed.
-/
lemma holonomy_norm (b : BoundaryTwist L) : ‖holonomy L b‖ = 1 := by sorry
/--
Proposed norm-one property of r^n for every integer n, including negative positions. This is the
scalar cancellation needed for actual adjoints, densities and site mixed CAR.
-/
lemma lift_phase_norm (b : BoundaryTwist L) (n : ℤ) : ‖liftPhase L b n‖ = 1 := by sorry
/--
Proposed multiplicative law r^(n+m)=r^n*r^m for integer displacement. It is the scalar transport
composition law; nonzero step is essential for unrestricted integer exponents.
-/
lemma lift_phase_add (b : BoundaryTwist L) (n m : ℤ) :
    liftPhase L b (n+m) = liftPhase L b n * liftPhase L b m := by sorry
/--
Proposed phase law for w signed laps: translating n by wL multiplies its phase by τ^w. This
distinguishes step transport from full-loop holonomy and covers multiple positive or negative
windings.
-/
lemma lift_phase_winding (b : BoundaryTwist L) (n w : ℤ) :
    liftPhase L b (n+w*(L : ℤ)) = holonomy L b^w * liftPhase L b n := by sorry
/--
Proposed identification of the angular construction's full-loop phase with exp(2πiβ). Positive L
is required to cancel the division by L in the exponential. It specifies the relation between
the real offset and scalar boundary condition.
-/
lemma angle_holonomy (β : ℝ) :
    holonomy L (angleTwist L β) = Complex.exp (((2*Real.pi*β : ℝ) : ℂ)*Complex.I) := by sorry
/--
Proposed coverage of every norm-one step record by some real β at positive L. The angle is not
claimed to be unique; distinct real lifts can describe the same step. This is a coverage
theorem, not a canonical choice of physical energy offset.
-/
lemma angle_twist_surjective (b : BoundaryTwist L) : ∃ β : ℝ, angleTwist L β = b := by sorry
/--
Proposed existence of a step record realizing any prescribed unit complex full-ring phase u. It
requires positive L and a norm-one hypothesis on u. Thus arbitrary scalar twisted boundary
conditions are represented, rather than only periodic and anti-periodic cases.
-/
lemma holonomy_surjective (u : ℂ) (hu : ‖u‖ = 1) :
    ∃ b : BoundaryTwist L, holonomy L b = u := by sorry
/--
Proposed full-loop phase one for the selected periodic step r=1. This is the trivial external
boundary condition and does not follow merely from fermionic grading.
-/
lemma periodic_holonomy : holonomy L (periodicTwist L) = 1 := by sorry
/--
Proposed full-loop phase -1 for the centered half-integer offset β=-1/2 at positive L. The per-
step phase is generally not -1; the minus sign appears after a complete lap.
-/
lemma antiperiodic_holonomy : holonomy L (antiperiodicTwist L) = -1 := by sorry
/--
Proposed invariance of full-loop phase under β ↦ β+z for integer z. Only holonomy is compared:
physical momentum labels and chosen per-step roots can change. This does not assert equality of
finite kinetic spectra.
-/
lemma angle_integer_holonomy (β : ℝ) (z : ℤ) :
    sameHolonomy L (angleTwist L (β+(z : ℝ))) (angleTwist L β) := by sorry
/--
Proposed change of the chosen step under β ↦ β+1: multiply it by the frozen canonical root ζ. It
makes the extra choice beyond holonomy explicit and fixes the positive Fourier orientation.
-/
lemma angle_root_shift (β : ℝ) :
    (angleTwist L (β+1)).step = (angleTwist L β).step * A01.canonicalRoot L := by sorry

/--
Proposed integer identity n=val([n])+wL, including negative n. Positive L relates Euclidean
division to the quotient representative. This arithmetic bridge supports lift/site and arbitrary
seam-transport statements.
-/
lemma winding_decomposition (n : ℤ) :
    n = (((n : Ch01.Lattice L).val : ℕ) : ℤ)+windingNumber L n*(L : ℤ) := by sorry
/--
Proposed update of the representative correction after w additional laps: multiply seamPhase by
τ^w. It handles negative winding using integer powers and the norm-one holonomy.
-/
lemma seam_phase_winding (b : BoundaryTwist L) (n w : ℤ) :
    seamPhase L b (n+w*(L : ℤ)) = holonomy L b^w*seamPhase L b n := by sorry
/--
Proposed finite orthogonality of the twisted Fourier kernels on the chosen L site
representatives. Both kernels use the same b, so conjugate external phases cancel and the sum is
L for equal modes and zero otherwise. Different twists require a separate mixed-kernel
statement.
-/
lemma twisted_character_orthogonality (b : BoundaryTwist L) (k p : Ch01.Band L) :
    (∑ x : Ch01.Lattice L,
      star (twistedCharacter L b k (x.val : ℤ))*twistedCharacter L b p (x.val : ℤ)) =
      if k=p then (L : ℂ) else 0 := by sorry
/--
Proposed recovery of a momentum annihilator from twisted site annihilators using conjugate
twisted kernels and the frozen normalization. The same b must occur in both factors for
cancellation. This allows downstream momentum operators to keep their existing definition while
using a twisted spatial presentation.
-/
lemma twisted_fourier_inverse (b : BoundaryTwist L) (k : Ch01.Band L) :
    Ch05.momentumAnnihilation L k = (A01.normalization L : ℂ) •
      ∑ x : Ch01.Lattice L, star (twistedCharacter L b k (x.val : ℤ)) •
        siteAnnihilation L b x := by sorry

/--
Proposed positive-sign Fourier expansion of the lifted twisted annihilator, with the existing
momentum operators and normalization. The external phase is carried by twistedCharacter, so
choosing APBC does not replace the integer mode carrier.
-/
lemma annihilation_fourier (b : BoundaryTwist L) (n : ℤ) :
    annihilation L b n = (A01.normalization L : ℂ) •
      ∑ k : Ch01.Band L, twistedCharacter L b k n • Ch05.momentumAnnihilation L k := by sorry
/--
Proposed equality of the lifted creator to the actual Hilbert adjoint of the lifted annihilator.
Complex scalar conjugation in creation is needed because taking an adjoint conjugates a scalar
multiplier.
-/
lemma creation_adjoint (b : BoundaryTwist L) (n : ℤ) :
    creation L b n = LinearMap.adjoint (annihilation L b n) := by sorry
/--
Proposed boundary law c_b(n+wL)=τ^w • c_b(n). The b parameter remains explicit, so later results
can quantify over arbitrary twist before specializing it. The equality is a proof obligation,
not an additional definition of the field.
-/
lemma annihilation_winding (b : BoundaryTwist L) (n w : ℤ) :
    annihilation L b (n+w*(L : ℤ)) = holonomy L b^w • annihilation L b n := by sorry
/--
Proposed boundary law for the creator, with conjugated holonomy star(τ^w). This reverses the
annihilator phase as required by adjointness; using the same unconjugated phase would generally
be wrong.
-/
lemma creation_winding (b : BoundaryTwist L) (n w : ℤ) :
    creation L b (n+w*(L : ℤ)) = star (holonomy L b^w) • creation L b n := by sorry
/--
Proposed expression of a lifted annihilator as seamPhase times its fundamental-domain site
section. This exposes the exact information discarded by converting n to its quotient residue
and applies to negative positions too.
-/
lemma lift_site_relation (b : BoundaryTwist L) (n : ℤ) :
    annihilation L b n = seamPhase L b n • siteAnnihilation L b (n : Ch01.Lattice L) := by sorry
/--
Proposed equality between the selected r=1 extension field and frozen CH05 positionAnnihilation.
This is the compatibility specialization for periodic calculations and does not change the
frozen operator definition.
-/
lemma periodic_field (n : ℤ) :
    annihilation L (periodicTwist L) n = Ch05.positionAnnihilation L (n : Ch01.Lattice L) := by sorry
/--
Proposed sign change of the selected APBC annihilator after one full lap. The integer argument
distinguishes n from n+L even though their quotient residues coincide.
-/
lemma antiperiodic_field (n : ℤ) :
    annihilation L (antiperiodicTwist L) (n+(L : ℤ)) = -annihilation L (antiperiodicTwist L) n := by sorry
/--
Proposed nonzero-action witness for every twisted lifted annihilator. It prevents boundary
detection and quotient-descent statements from being satisfied trivially by the zero operator;
multiplication by a unit scalar preserves the frozen nonzero field.
-/
lemma annihilation_ne_zero (b : BoundaryTwist L) (n : ℤ) : annihilation L b n ≠ 0 := by sorry
/--
Proposed criterion for the lifted field to be an ordinary function of the quotient residue:
precisely holonomy one. The existence direction retains a function on ZMod L; the converse uses
a nonzero field to detect a nontrivial lap phase. A fundamental-domain section exists even when
this stronger descent property fails.
-/
lemma quotient_descent_iff (b : BoundaryTwist L) :
    (∃ f : Ch01.Lattice L → Ch05.Operators L, ∀ n : ℤ, annihilation L b n = f (n : Ch01.Lattice L)) ↔
      holonomy L b = 1 := by sorry
/--
Proposed vanishing anticommutator of twisted annihilators at any two selected quotient sites.
Both factors are scalar rescalings of frozen CAR generators, so the pure annihilation relation
survives arbitrary unit twist.
-/
lemma site_annihilation_car (b : BoundaryTwist L) (x y : Ch01.Lattice L) :
    A02.anticommutator (siteAnnihilation L b x) (siteAnnihilation L b y) = 0 := by sorry
/--
Proposed vanishing anticommutator of twisted creators at any two selected quotient sites.
Conjugate scalar rescaling preserves the pure creation CAR.
-/
lemma site_creation_car (b : BoundaryTwist L) (x y : Ch01.Lattice L) :
    A02.anticommutator (siteCreation L b x) (siteCreation L b y) = 0 := by sorry
/--
Proposed canonical mixed CAR on the selected site representatives, with identity coefficient one
only when x=y. Unit modulus cancels the two scalar phases on the coincident-site branch. The
symbol • multiplies the identity operator by the displayed complex coefficient.
-/
lemma site_mixed_car (b : BoundaryTwist L) (x y : Ch01.Lattice L) :
    A02.anticommutator (siteAnnihilation L b x) (siteCreation L b y) =
      (if x=y then (1 : ℂ) else 0) • (1 : Ch05.Operators L) := by sorry
/--
Proposed mixed CAR on integer lifts: equal residues carry the relative phase r^(n-m), while
unequal residues give zero. This keeps holonomy visible when two arguments represent the same
site after different laps; replacing the coefficient by one would erase the seam.
-/
lemma lifted_mixed_car (b : BoundaryTwist L) (n m : ℤ) :
    A02.anticommutator (annihilation L b n) (creation L b m) =
      (if (n : Ch01.Lattice L)=(m : Ch01.Lattice L) then liftPhase L b (n-m) else 0) •
        (1 : Ch05.Operators L) := by sorry
/--
Proposed identification of same-twist local density with the frozen position number operator.
The conjugate creator phase cancels the annihilator phase exactly. This establishes twist
independence for this observable rather than assuming it for all operators.
-/
lemma density_untwisted (b : BoundaryTwist L) (n : ℤ) :
    density L b n = Ch05.positionNumber L (n : Ch01.Lattice L) := by sorry
/--
Proposed strict periodicity of same-species density for every unit twist. Full-lap phases cancel
in the ordered bilinear, even when the individual fermion fields are anti-periodic or otherwise
twisted.
-/
lemma density_periodic (b : BoundaryTwist L) (n : ℤ) : density L b (n+(L : ℤ)) = density L b n := by sorry
/--
Proposed equality of the twisted-generator local algebra and frozen CH06 localAlgebra on the
same region. Nonzero scalar multipliers generate the same complex algebra. After proof, later
chapters may use CH06 local-algebra theorems while keeping Ch06Ext fields and transport.
-/
lemma local_algebra_eq (b : BoundaryTwist L) (I : Ch06.Region L) : localAlgebra L b I = Ch06.localAlgebra L I := by sorry
/--
Proposed equality of the twisted and frozen parity-homogeneous local subspaces. Both
presentations use the same parity map; the local-algebra identification therefore also transfers
grading. This bridge does not identify their spatial transport data.
-/
lemma local_part_eq (b : BoundaryTwist L) (I : Ch06.Region L) (σ : Ch06.Degree) :
    localPart L b I σ = Ch06.localPart L I σ := by sorry
/--
Proposed disjoint-region exchange relation for the twisted local parts. The sign depends on the
parity degrees σ and τ, not on spatial holonomy. Disjoint support is necessary; this is not a
boundary condition for going around the ring.
-/
lemma graded_locality (b : BoundaryTwist L) (I J : Ch06.Region L) (hIJ : Disjoint I J)
    (σ τ : Ch06.Degree) (A B : Ch05.Operators L)
    (hA : A ∈ localPart L b I σ) (hB : B ∈ localPart L b J τ) :
    A*B = (-1 : ℂ)^(σ.val*τ.val) • (B*A) := by sorry

/--
Proposed basis-action formula for the complete diagonal translation definition. It supplies the
concrete scalar to check group laws, adjoints and covariance on actual occupation kets. The •
here multiplies a Fock vector, rather than an operator.
-/
lemma translation_ket (b : BoundaryTwist L) (m : ℤ) (S : Ch06.Occupation L) :
    translation L b m (A02.ket S) =
      (b.step^(-m*(S.card : ℤ))*A01.canonicalRoot L^(-m*Ch05.occupationEnergy L S)) • A02.ket S := by sorry
/--
Proposed identity action for zero displacement. Together with translation_add it supplies the
neutral element of the integer translation representation.
-/
lemma translation_zero (b : BoundaryTwist L) : translation L b 0 = 1 := by sorry
/--
Proposed representation law T(m+n)=T(m)*T(n) on the same twist b. Operator multiplication means
composition; all integer shifts are allowed, including inverses. Different twists are not
silently combined.
-/
lemma translation_add (b : BoundaryTwist L) (m n : ℤ) :
    translation L b (m+n) = translation L b m * translation L b n := by sorry
/--
Proposed actual-adjoint identity T(m)†=T(-m). Unit phases in the diagonal basis action are the
needed input; this is not assumed when defining transport.
-/
lemma translation_adjoint (b : BoundaryTwist L) (m : ℤ) :
    LinearMap.adjoint (translation L b m) = translation L b (-m) := by sorry
/--
Proposed two-sided unitary identities using the actual Hilbert adjoint. Both orders are stated
so inverse transport is certified on the complete finite Fock carrier.
-/
lemma translation_unitary (b : BoundaryTwist L) (m : ℤ) :
    translation L b m * LinearMap.adjoint (translation L b m) = 1 ∧
      LinearMap.adjoint (translation L b m) * translation L b m = 1 := by sorry
/--
Proposed expansion of the linear transport definition as the ordered product T(m)*A*T(-m). This
fixes which map acts on which side and avoids an accidental reversal of conjugation.
-/
lemma transport_apply (b : BoundaryTwist L) (m : ℤ) (A : Ch05.Operators L) :
    transport L b m A = translation L b m*A*translation L b (-m) := by sorry
/--
Proposed composition law for operator transport at a fixed b. Transport by n followed by m
agrees with transport by m+n; group identities must be established from translation, not from
the region shift alone.
-/
lemma transport_add (b : BoundaryTwist L) (m n : ℤ) (A : Ch05.Operators L) :
    transport L b (m+n) A = transport L b m (transport L b n A) := by sorry
/--
Proposed compatibility of transport with the actual Hilbert adjoint of operators. It is the
star-preservation needed by covariance of local creator/annihilator algebras.
-/
lemma transport_star (b : BoundaryTwist L) (m : ℤ) (A : Ch05.Operators L) :
    transport L b m (LinearMap.adjoint A) = LinearMap.adjoint (transport L b m A) := by sorry
/--
Proposed packaging of the complete transport map as an actual complex algebra equivalence, with
adjoint preservation explicitly included. Existence requires proving multiplication, identity
and inverse properties. This avoids constructing certified automorphism data from unproved stub
lemmas.
-/
lemma transport_automorphism_exists (b : BoundaryTwist L) (m : ℤ) :
    ∃ f : Ch05.Operators L ≃ₐ[ℂ] Ch05.Operators L,
      (∀ A, f A = transport L b m A) ∧
      ∀ A, f (LinearMap.adjoint A) = LinearMap.adjoint (f A) := by sorry
/--
Proposed covariance T(m)c_b(n)T(-m)=c_b(n+m) for all integer lifts. The same b is required in
the translation and field; the negative translation exponents were selected to match this
positive Fourier convention.
-/
lemma transport_annihilation (b : BoundaryTwist L) (m n : ℤ) :
    transport L b m (annihilation L b n) = annihilation L b (n+m) := by sorry
/--
Proposed creator covariance under the same transport and integer shift. It should follow
compatibly with actual adjoints, retaining conjugate field phases.
-/
lemma transport_creation (b : BoundaryTwist L) (m n : ℤ) :
    transport L b m (creation L b n) = creation L b (n+m) := by sorry
/--
Proposed transport law on selected quotient-site representatives, with the exact seamPhase of
x.val+m. The shifted quotient site alone is insufficient when the lifted displacement crosses
the seam; arbitrary negative and multiple-lap m are included.
-/
lemma site_transport (b : BoundaryTwist L) (m : ℤ) (x : Ch01.Lattice L) :
    transport L b m (siteAnnihilation L b x) =
      seamPhase L b ((x.val : ℤ)+m) • siteAnnihilation L b (x+(m : Ch01.Lattice L)) := by sorry
/--
Proposed one-step boundary transition from lift L-1 to lift L, expressed as τ times the field at
zero. It displays the physical twisted boundary term in the chosen positive orientation.
-/
lemma seam_transport (b : BoundaryTwist L) :
    transport L b 1 (annihilation L b ((L : ℤ)-1)) = holonomy L b • annihilation L b 0 := by sorry
/--
Proposed equivalence of membership in a local algebra before and after region translation.
Individual generators acquire nonzero seam scalars, which preserve the generated algebra. The
statement includes both directions through invertible transport.
-/
lemma local_transport (b : BoundaryTwist L) (m : ℤ) (I : Ch06.Region L) :
    ∀ A, A ∈ localAlgebra L b I ↔ transport L b m A ∈ localAlgebra L b (shiftRegion L m I) := by sorry
/--
Proposed local transport covariance with parity degree preserved. It combines local-algebra
covariance and compatibility with the fixed parity map, keeping even and odd subspaces distinct.
-/
lemma local_part_transport (b : BoundaryTwist L) (m : ℤ) (I : Ch06.Region L) (σ : Ch06.Degree) :
    ∀ A, A ∈ localPart L b I σ ↔ transport L b m A ∈ localPart L b (shiftRegion L m I) σ := by sorry
/--
Proposed invariance of the frozen total-number operator under twisted spatial transport. Both
translation and number are diagonal in occupation data; this does not imply that particle-
lowering fields preserve number.
-/
lemma translation_preserves_number (b : BoundaryTwist L) (m : ℤ) :
    transport L b m (Ch05.totalNumber L) = Ch05.totalNumber L := by sorry
/--
Proposed invariance of the frozen periodic-reference bareHamiltonian under this diagonal
translation. This Hamiltonian uses integer labels; the theorem does not identify it with a
β-shifted physical energy or an arbitrary nonlinear dispersion.
-/
lemma translation_preserves_hamiltonian (b : BoundaryTwist L) (m : ℤ) :
    transport L b m (Ch05.bareHamiltonian L) = Ch05.bareHamiltonian L := by sorry
/--
Proposed invariance of the actual occupation-parity operator under spatial transport. Parity
remains the grading structure used by CH06, separate from the arbitrary boundary holonomy.
-/
lemma translation_preserves_parity (b : BoundaryTwist L) (m : ℤ) :
    transport L b m (Ch06.parityOperator L) = Ch06.parityOperator L := by sorry
/--
Proposed equality T(L)=gauge(τ) on the full Fock space. Its basis factor is τ^(-#S), so full-lap
translation need not be the identity even though quotient sites return to themselves.
-/
lemma full_ring_translation (b : BoundaryTwist L) :
    translation L b (L : ℤ) = gauge L (holonomy L b) := by sorry
/--
Proposed agreement of translation by a natural number of steps with the corresponding power of
one-step translation. Integer translation_add supplies the representation structure; full-ring
powers then expose holonomy.
-/
lemma translation_power (b : BoundaryTwist L) (m : ℕ) :
    translation L b (m : ℤ) = translation L b 1 ^ m := by sorry
/--
Proposed identification of the selected APBC full-lap translation with actual occupation parity.
This follows from τ=-1 and the charge-gauge basis factor, not from graded locality alone.
-/
lemma apbc_full_ring_parity :
    translation L (antiperiodicTwist L) (L : ℤ) = Ch06.parityOperator L := by sorry
/--
Proposed full-lap transport action on an annihilator: multiply it by the boundary phase τ. It
makes loop transport observable at the operator level even though the underlying local algebra
is unchanged.
-/
lemma holonomy_acts_on_field (b : BoundaryTwist L) (n : ℤ) :
    transport L b (L : ℤ) (annihilation L b n) = holonomy L b • annihilation L b n := by sorry
/--
Proposed detection of equality of two holonomies by the full-lap action on the nonzero b-fields.
Only the scalar phase from c is compared; the statement does not equate the two field families
or their chosen step roots.
-/
lemma holonomy_detected_iff (b c : BoundaryTwist L) :
    (∀ n : ℤ, transport L b (L : ℤ) (annihilation L b n) =
      holonomy L c • annihilation L b n) ↔ sameHolonomy L b c := by sorry
/--
Proposed relation between fields defined by any two step choices: multiply the b-field by
(c.step/b.step)^n. The denominator is nonzero by its norm certificate. This is a position-
dependent scalar identity, not an assertion of a Fock-space gauge equivalence of kinetic
Hamiltonians.
-/
lemma change_trivialization_field (b c : BoundaryTwist L) (n : ℤ) :
    annihilation L c n = (c.step/b.step)^n • annihilation L b n := by sorry
/--
Proposed periodicity of the step-ratio phase when the two records have equal holonomy. It is the
compatibility needed for an alternative fundamental-domain convention on the same scalar
boundary sector.
-/
lemma trivialization_ratio_periodic (b c : BoundaryTwist L) (hbc : sameHolonomy L b c) (n : ℤ) :
    (c.step/b.step)^(n+(L : ℤ)) = (c.step/b.step)^n := by sorry
/--
Proposed actual basis action of the complete source-sector zeroMode map. The charge is
#S-referenceCharge before any creator or annihilator acts; this order matters in a later Klein
factor product.
-/
lemma zero_mode_ket (b : BoundaryTwist L) (n referenceCharge : ℤ) (S : Ch06.Occupation L) :
    zeroMode L b n referenceCharge (A02.ket S) =
      (liftPhase L b n*A01.canonicalRoot L^(n*((S.card : ℤ)-referenceCharge))) • A02.ket S := by sorry
/--
Proposed full-winding law of zeroMode with the same τ as the comparison fermion field. Integer
source charge contributes a trivial full-period ζ factor, so fixed external holonomy is not
dynamically changed by lowering that charge.
-/
lemma zero_mode_winding (b : BoundaryTwist L) (n referenceCharge w : ℤ) :
    zeroMode L b (n+w*(L : ℤ)) referenceCharge = holonomy L b^w • zeroMode L b n referenceCharge := by sorry
/--
Proposed unitary norm identity Z†Z=1 for the actual diagonal zeroMode map. All its basis phases
have unit modulus; no analytic exponential of an unbounded operator is being introduced.
-/
lemma zero_mode_unitary (b : BoundaryTwist L) (n referenceCharge : ℤ) :
    LinearMap.adjoint (zeroMode L b n referenceCharge)*zeroMode L b n referenceCharge = 1 := by sorry
/--
Proposed ordered relation Z*c_k†=ζ^n • (c_k†*Z). Creation raises source occupation by one,
changing the charge phase by ζ^n. The external r^n factor stays the same on both sides.
-/
lemma zero_mode_creation_order (b : BoundaryTwist L) (n referenceCharge : ℤ) (k : Ch01.Band L) :
    zeroMode L b n referenceCharge*Ch05.momentumCreation L k =
      A01.canonicalRoot L^n • (Ch05.momentumCreation L k*zeroMode L b n referenceCharge) := by sorry
/--
Proposed ordered relation Z*c_k=ζ^(-n) • (c_k*Z). Annihilation lowers occupation by one; the
position-dependent charge factor changes while fixed full-loop external holonomy remains
unchanged.
-/
lemma zero_mode_annihilation_order (b : BoundaryTwist L) (n referenceCharge : ℤ) (k : Ch01.Band L) :
    zeroMode L b n referenceCharge*Ch05.momentumAnnihilation L k =
      A01.canonicalRoot L^(-n) • (Ch05.momentumAnnihilation L k*zeroMode L b n referenceCharge) := by sorry

end Fields

/--
The separate Jordan–Wigner sector convention τ_JW(p)=-(-1)^p for integer total particle count p.
Even occupation selects APBC and odd occupation selects periodicity. This is a scalar dictionary
awaiting a separately specified spin Hamiltonian/string correspondence, not a replacement for a
fixed external twist.
-/
noncomputable def jwHolonomy (particles : ℤ) : ℂ := -((-1 : ℂ)^particles)

/--
Choose the centered APBC record in an even-particle source sector and the periodic record
otherwise. This is sector-indexed boundary data. Odd particle-changing operators map between
different such records, so later spin-model intertwiners must state both source and target
sectors.
-/
noncomputable def jwSectorTwist (L : ℕ) (particles : ℤ) : BoundaryTwist L :=
  if Even particles then antiperiodicTwist L else periodicTwist L

/--
Proposed APBC value -1 of the JW dictionary in an even-particle sector. The explicit parity
hypothesis states which sector is being selected; no spin-chain equivalence is asserted here.
-/
lemma jw_even (particles : ℤ) (hp : Even particles) : jwHolonomy particles = -1 := by sorry
/--
Proposed periodic value one of the JW dictionary in an odd-particle sector. This follows the
recorded string convention and should not be generalized to an unspecified spin boundary
convention.
-/
lemma jw_odd (particles : ℤ) (hp : Odd particles) : jwHolonomy particles = 1 := by sorry
/--
Proposed agreement between the selected sector's step record and its JW full-loop phase at
positive L. This connects two definitions of the sector dictionary, rather than proving a
physical Jordan–Wigner operator identity.
-/
lemma jw_sector_holonomy (L : ℕ) [NeZero L] (particles : ℤ) :
    holonomy L (jwSectorTwist L particles) = jwHolonomy particles := by sorry
/--
Proposed reversal of JW holonomy when the total particle count decreases by one. It exposes why
an odd particle-changing map in a spin model cannot be treated as staying inside a single fixed-
JW-twist sector.
-/
lemma jw_parity_flip (particles : ℤ) : jwHolonomy (particles-1) = -jwHolonomy particles := by sorry

/--
The real linear-dispersion label k+β, in dimensionless momentum units before an optional 2π/L
prefactor. This retains β explicitly because equal boundary phases can have different real
lifts. Connect it to fields by choosing b=angleTwist L β in the downstream model.
-/
def physicalMomentum (L : ℕ) (β : ℝ) (k : Ch01.Band L) : ℝ := (k.val : ℝ)+β

/--
Sum the real shifted momentum labels over the occupied finite set S. This implements uniform
linear dispersion only; β contributes once per occupied mode. Its connection to a twisted field
requires the same angular choice b=angleTwist L β.
-/
def physicalOccupationEnergy (L : ℕ) (β : ℝ) (S : Ch06.Occupation L) : ℝ :=
  ∑ k ∈ S, physicalMomentum L β k

/--
Subtract the energy of the existing CH05 sea from the shifted occupation energy. Both terms use
the same β and reference occupations, so the shift is β times relative charge. Choosing another
physical sea requires a separate definition and bridge.
-/
def physicalRelativeEnergy (L : ℕ) (β : ℝ) (S : Ch06.Occupation L) : ℝ :=
  physicalOccupationEnergy L β S - physicalOccupationEnergy L β (Ch05.seaConfiguration L)

/--
The real charge-energy polynomial N(N+1)/2+βN associated with the same-sea linear convention.
Its definition alone does not prove that it is a minimum or that the charge sector is
admissible; those obligations belong to CH07. At APBC it can be half-integral, so it must not
replace an integer excitation label indiscriminately.
-/
noncomputable def physicalGroundEnergy (β : ℝ) (N : ℤ) : ℝ := (N : ℝ)*((N : ℝ)+1)/2+β*(N : ℝ)

/--
Proposed decomposition of shifted occupation energy into the frozen integer sum plus β times
total particle count. This states its parameter dependency explicitly and fixes the distinction
between total and relative charge.
-/
lemma physical_energy_shift (L : ℕ) (β : ℝ) (S : Ch06.Occupation L) :
    physicalOccupationEnergy L β S = (Ch05.occupationEnergy L S : ℝ)+β*(S.card : ℝ) := by sorry
/--
Proposed same-sea subtraction formula: frozen relative integer energy plus β times S.card minus
the sea cardinality. A uniform shift and identical reference sea are built into the definitions;
this is not a result for arbitrary dispersion.
-/
lemma physical_relative_shift (L : ℕ) (β : ℝ) (S : Ch06.Occupation L) :
    physicalRelativeEnergy L β S =
      ((Ch05.occupationEnergy L S-Ch05.seaEnergy L : ℤ) : ℝ)+
      β*((S.card : ℝ)-((Ch05.seaConfiguration L).card : ℝ)) := by sorry
/--
Proposed β independence after subtracting the matching charge polynomial from the physical
relative energy. Positive even length supplies the half-filled reference charge S.card-h. This
algebraic bridge does not itself prove excitation nonnegativity or ground minimality, and it
must not be applied with a different sea or unmatched β.
-/
lemma excitation_twist_cancel (h : ℕ) (hh : 0 < h) (β : ℝ) (S : Ch06.Occupation (2*h)) :
    physicalRelativeEnergy (2*h) β S-physicalGroundEnergy β ((S.card : ℤ)-(h : ℤ)) =
      ((Ch05.occupationEnergy (2*h) S-Ch05.seaEnergy (2*h) : ℤ) : ℝ)-
        physicalGroundEnergy 0 ((S.card : ℤ)-(h : ℤ)) := by sorry
/--
Proposed specialization of the charge polynomial at β=-1/2 to N²/2. This makes the physical APBC
energy convention explicit, including half-integral values for odd N, while leaving the existing
integer reference energy unchanged.
-/
lemma apbc_ground_energy (N : ℤ) : physicalGroundEnergy (-1/2) N = (N : ℝ)^2/2 := by sorry

end Bosonize.Ch06Ext
```
