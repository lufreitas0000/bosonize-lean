# Chapter 5 position and momentum fermions lab notebook

Status (2026-10-09): **Phase A draft; unlocked and unproved, awaiting interface review.** Lean module: `BosonizeStubs/Ch05Fermions.lean`. Task baseline: frozen Core checkpoint `3c2cf5a`. Authorization covers CH05 and parallel CH06 drafting, stopping before locking, proof development or promotion.

## Source reconciliation and review choices

Read [CH05](../../../notes/md/ch05_fermions_lattice_band.md), [A01](../../../notes/appendices/a01_fourier_scalars_and_characters.md), [A04](../../../notes/appendices/a04_density_partitions_and_sugawara.md), [TOC](../../../notes/md/TOC.md), [source audit](../../../docs/audit/reference_notes_lean_audit.md) and [proof corrections](../../../note/proof_suggestions_revision_2026-10-09.md). No CH05-specific suggestion is available: the current checkout has no remaining `docs/stub_suggestion/` or `docs/proof_suggestion/` directories. Inline proof sketches remain advisory. The TOC's claim that only CH01/CH02 are frozen is historical; current Core includes CH01–CH04, A01 and finite-CAR A02. Source notes are unchanged.

Adopt positive annihilation and negative creation character kernels, one real `A01.normalization` scalar cast into ℂ, the canonical primitive root, and the frozen positive-Nyquist band. Reuse A01's character/conjugation/orthogonality proofs rather than reimplementing them. Character negation is ordinary integer negation, so no negative-Nyquist membership is required. `LinearMap.adjoint` is the actual finite-dimensional Hilbert adjoint; its installed signature was verified by native MCP hover.

**Explicit proposed generalization:** the Fourier/CAR layer uses any positive `L` (`[NeZero L]`), since evenness is unnecessary there. This broadens the notes' physical convention and needs review. Half-filled sea cardinality and triangular-energy statements specialize to exactly `L=2*h`, `h>0`; no half-filling assertion is made for odd sizes. Momentum and signed-energy definitions do not require positive size.

## Carrier and definitions

Sixteen complete definitions/abbreviations. `FockSpace L` is exactly `A02.FockSpace (Ch01.Band L)`; `Operators L` is its complex-linear endomorphism algebra. Momentum operators reuse CH04. Position operators are finite sums with `1/sqrt(L)`, using the same occupation carrier. A position occupation basis is not silently identified with the momentum basis.

`occupationEnergy` is an integer sum of signed band labels. `bareHamiltonian` weights momentum numbers; `seaConfiguration` fills all `k.val≤0` in the actual band. `seaEnergy` is its integer sum and `seaKet` its basis ket. `shiftedHamiltonian` subtracts that scalar times identity. The triangular formula is a theorem stub, never an assumption used in a definition; negative energies are not clipped to naturals. At `h=1` the sea energy is zero, so nonzero bare-sea-action witnesses require `h≥2`, separately from the always-nonzero sea ket.

## Proposed obligations and proof order

All 35 lemmas have exactly one `:= by sorry` and remain unproved.

| Group | Obligations and future proof order |
| --- | --- |
| Fourier CAR | Prove adjoints using conjugate kernels, expand all three CAR sums, apply momentum CAR and orthogonality, cancel the single normalization law; only then construct position CAR. |
| Recovery and observables | Both inverse transforms precede total-number invariance; reuse A02 algebraic CAR for number idempotency, adjoints, commutation and number commutators. |
| Witnesses and parity | Empty-occupation annihilation, nonzero position creation and parity oddness use actual CH04 occupation/parity action. Nonzero witness statements are stubs, not established evidence. |
| Signed energies | Basis spectrum, self-adjointness, bare/shifted commutators follow diagonal number action, retaining integer-to-complex casts. |
| Sea | Count/sum `[-h+1,0]` for `h>0`; derive bare/shifted sea action, triangular energy, the `h=1` zero endpoint, and `h≥2` nonzero witness. |

No budgets, density/Sugawara layer, sector-ground proof, normal symbols, analytic limit or thermodynamic construction is implemented. A04 informs conventions and later dependencies only.

## Parallel CH06 interface and attribution

The primary formalizer drafts CH05; one delegated formalizer drafts CH06, both using the repository formalizer skill. CH06 consumes position generators, actual-adjoint, inverse-transform and parity contracts. Its algebra and word definitions can be drafted in parallel; future Phase B must first prove the CH05 contracts used by CH06. Combined elaboration is not proof of either chapter's statements.

## Phase A validation and review boundary

Fresh direct compilation and the module build pass with exactly 35 expected declaration-uses-sorry warnings, no errors or extra linter warnings. Native MCP diagnostics are successful, complete and contain exactly these 35 warnings, with no timeout or failed dependencies. Hover checks the adjoint API. Native search fails because its server PATH lacks `rg`; shell sources and compiler inspection supply retrieval. Diagnostics and hover work, so this is a search-tool limitation.

Fresh axiom inspection verifies all 16 definitions/abbreviations with only standard axioms and no `sorryAx`; all 35 theorem stubs expose `sorryAx`. Definitions consume no unproved chapter lemma. Existing approved interfaces, six Core hashes and manifests remain unchanged. Full strict CI must reject these new unlocked modules until review; do not treat that expected rejection as a compiler failure or lock them prematurely.

Joint validation: both libraries build, all 69 guard regression tests pass, and all six existing Core hashes remain unchanged. Non-strict verification against `3c2cf5a` passes 182 approved statements and 152 commands while naming the two new drafts. Strict verification rejects exactly CH05 and CH06 as unlocked, as required before review. Active/legacy manifests, dependency manifest, toolchain and the Core aggregator remain byte-identical to the baseline.

Review the generic positive-size layer, kernel signs, integer shift and witness hypotheses together with CH06's grading/locality/matrix-unit interface. Approval precedes locking and Phase B. No proof work or promotion is performed in this draft.

## Source provenance

| Source | SHA-256 |
| --- | --- |
| `notes/md/ch05_fermions_lattice_band.md` | `0a7a26d8890640541d39e918e3f3f87aeb8cb625914a34dc0709cfc73ff43051` |
| `notes/appendices/a01_fourier_scalars_and_characters.md` | `0b65cf6f5ed73a59ef5d25b2b502c34c4315cb5ce1df67cb690c3defba70b165` |
| `notes/appendices/a04_density_partitions_and_sugawara.md` | `32016e054e850c9796ae58d1493f1c552c71ab42607fc5f91b8b1878d37e6e9e` |
| `notes/md/TOC.md` | `5ea6b32bdecf8f9c65a345dc12356ff767b176c0b131e32acdb836778b054977` |
| `docs/audit/reference_notes_lean_audit.md` | `35245d3a8ed87e5ed1f31947132fb272848cfc8ff83236af49c9c45dc0bb4877` |
| `note/proof_suggestions_revision_2026-10-09.md` | `1db5f28b3e392d3b400ccc219ac640778fc5ceabc5cba17dfeb44b225a1b383c` |

## Definition axiom audit

```text
'Bosonize.Ch05.FockSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.Operators' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.momentumAnnihilation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.momentumCreation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.momentumNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.positionAnnihilation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.positionCreation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.positionNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.totalNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.occupationEnergy' depends on axioms: [propext, Quot.sound]
'Bosonize.Ch05.bareHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.seaConfiguration' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.seaEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.seaKet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.shiftedHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.parity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Exact Lean source snapshot

Module SHA-256: `4433a21d4e418c9c745b213317e736425ccea1febbab527c34f429060d772446`. This block matches the draft byte-for-byte.

```lean
module

public import Bosonize.Core.A01FourierCharacters
public import Bosonize.Core.Ch03Fourier
public import Bosonize.Core.Ch04CARFock

/-!
# Chapter 5: position and momentum fermions
Phase A: complete definitions and one-sorry review stubs.
The Fourier layer works for positive L; physical sea formulas specialize to L = 2*h, h > 0.
-/

@[expose] public section

namespace Bosonize.Ch05

open scoped BigOperators

abbrev FockSpace (L : ℕ) := A02.FockSpace (Ch01.Band L)
abbrev Operators (L : ℕ) := Module.End ℂ (FockSpace L)

noncomputable def momentumAnnihilation (L : ℕ) (k : Ch01.Band L) : Operators L :=
  Ch04.annihilation k

noncomputable def momentumCreation (L : ℕ) (k : Ch01.Band L) : Operators L :=
  Ch04.creation k

noncomputable def momentumNumber (L : ℕ) (k : Ch01.Band L) : Operators L :=
  momentumCreation L k * momentumAnnihilation L k

/-- Positive character kernel for annihilators, with the real unitary normalization. -/
noncomputable def positionAnnihilation (L : ℕ) [NeZero L]
    (x : Ch01.Lattice L) : Operators L :=
  (A01.normalization L : ℂ) • ∑ k : Ch01.Band L,
    A01.bandCharacter L (A01.canonicalRoot L) k x • momentumAnnihilation L k

/-- Ordinary integer negation in the character; no negative-band membership is assumed. -/
noncomputable def positionCreation (L : ℕ) [NeZero L]
    (x : Ch01.Lattice L) : Operators L :=
  (A01.normalization L : ℂ) • ∑ k : Ch01.Band L,
    A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) • momentumCreation L k

noncomputable def positionNumber (L : ℕ) [NeZero L]
    (x : Ch01.Lattice L) : Operators L :=
  positionCreation L x * positionAnnihilation L x

noncomputable def totalNumber (L : ℕ) : Operators L :=
  ∑ k : Ch01.Band L, momentumNumber L k

/-- Integer spectrum, without clipping negative bare energies. -/
def occupationEnergy (L : ℕ) (S : A02.Occupation (Ch01.Band L)) : ℤ :=
  ∑ k ∈ S, k.val

noncomputable def bareHamiltonian (L : ℕ) : Operators L :=
  ∑ k : Ch01.Band L, (k.val : ℂ) • momentumNumber L k

/-- Fill all nonpositive labels in the actual positive-Nyquist band. -/
def seaConfiguration (L : ℕ) : A02.Occupation (Ch01.Band L) :=
  Finset.univ.filter (fun k => k.val ≤ 0)

def seaEnergy (L : ℕ) : ℤ := occupationEnergy L (seaConfiguration L)

noncomputable def seaKet (L : ℕ) : FockSpace L := A02.ket (seaConfiguration L)

noncomputable def shiftedHamiltonian (L : ℕ) : Operators L :=
  bareHamiltonian L - (seaEnergy L : ℂ) • (1 : Operators L)

noncomputable def parity (L : ℕ) : Operators L := Ch04.parity

section Fourier
variable (L : ℕ) [NeZero L]

lemma position_creation_eq_adjoint (x : Ch01.Lattice L) :
    positionCreation L x = LinearMap.adjoint (positionAnnihilation L x) := by sorry

lemma position_annihilation_eq_adjoint (x : Ch01.Lattice L) :
    positionAnnihilation L x = LinearMap.adjoint (positionCreation L x) := by sorry

lemma position_annihilation_car (x y : Ch01.Lattice L) :
    A02.anticommutator (positionAnnihilation L x) (positionAnnihilation L y) = 0 := by sorry

lemma position_creation_car (x y : Ch01.Lattice L) :
    A02.anticommutator (positionCreation L x) (positionCreation L y) = 0 := by sorry

lemma position_mixed_car (x y : Ch01.Lattice L) :
    A02.anticommutator (positionAnnihilation L x) (positionCreation L y) =
      (if x = y then (1 : ℂ) else 0) • (1 : Operators L) := by sorry

lemma position_car_exists : ∃ R : A02.CAR (Ch01.Lattice L) (FockSpace L),
    R.annihilation = positionAnnihilation L ∧ R.creation = positionCreation L := by sorry

lemma inverse_annihilation (k : Ch01.Band L) :
    momentumAnnihilation L k = (A01.normalization L : ℂ) •
      ∑ x : Ch01.Lattice L,
        A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) •
          positionAnnihilation L x := by sorry

lemma inverse_creation (k : Ch01.Band L) :
    momentumCreation L k = (A01.normalization L : ℂ) •
      ∑ x : Ch01.Lattice L,
        A01.bandCharacter L (A01.canonicalRoot L) k x • positionCreation L x := by sorry

lemma total_number_position :
    (∑ x : Ch01.Lattice L, positionNumber L x) = totalNumber L := by sorry

lemma position_number_idempotent (x : Ch01.Lattice L) :
    positionNumber L x * positionNumber L x = positionNumber L x := by sorry

lemma position_number_adjoint (x : Ch01.Lattice L) :
    LinearMap.adjoint (positionNumber L x) = positionNumber L x := by sorry

lemma position_number_commute (x y : Ch01.Lattice L) :
    positionNumber L x * positionNumber L y = positionNumber L y * positionNumber L x := by sorry

lemma position_annihilation_vacuum (x : Ch01.Lattice L) :
    positionAnnihilation L x (A02.ket ∅) = 0 := by sorry

lemma position_creation_vacuum_ne_zero (x : Ch01.Lattice L) :
    positionCreation L x (A02.ket ∅) ≠ 0 := by sorry

lemma parity_position_creation (x : Ch01.Lattice L) :
    parity L * positionCreation L x = -(positionCreation L x * parity L) := by sorry

lemma parity_position_annihilation (x : Ch01.Lattice L) :
    parity L * positionAnnihilation L x = -(positionAnnihilation L x * parity L) := by sorry

lemma total_number_position_creation_commutator (x : Ch01.Lattice L) :
    A02.commutator (totalNumber L) (positionCreation L x) = positionCreation L x := by sorry

lemma total_number_position_annihilation_commutator (x : Ch01.Lattice L) :
    A02.commutator (totalNumber L) (positionAnnihilation L x) = -positionAnnihilation L x := by sorry

end Fourier

section Energy
variable (L : ℕ)

lemma total_number_ket (S : A02.Occupation (Ch01.Band L)) :
    totalNumber L (A02.ket S) = (S.card : ℂ) • A02.ket S := by sorry

lemma bare_hamiltonian_ket (S : A02.Occupation (Ch01.Band L)) :
    bareHamiltonian L (A02.ket S) = (occupationEnergy L S : ℂ) • A02.ket S := by sorry

lemma shifted_hamiltonian_ket (S : A02.Occupation (Ch01.Band L)) :
    shiftedHamiltonian L (A02.ket S) =
      ((occupationEnergy L S - seaEnergy L : ℤ) : ℂ) • A02.ket S := by sorry

lemma bare_hamiltonian_adjoint :
    LinearMap.adjoint (bareHamiltonian L) = bareHamiltonian L := by sorry

lemma shifted_hamiltonian_adjoint :
    LinearMap.adjoint (shiftedHamiltonian L) = shiftedHamiltonian L := by sorry

lemma bare_creation_commutator (k : Ch01.Band L) :
    A02.commutator (bareHamiltonian L) (momentumCreation L k) =
      (k.val : ℂ) • momentumCreation L k := by sorry

lemma bare_annihilation_commutator (k : Ch01.Band L) :
    A02.commutator (bareHamiltonian L) (momentumAnnihilation L k) =
      (-k.val : ℂ) • momentumAnnihilation L k := by sorry

lemma shifted_creation_commutator (k : Ch01.Band L) :
    A02.commutator (shiftedHamiltonian L) (momentumCreation L k) =
      (k.val : ℂ) • momentumCreation L k := by sorry

lemma shifted_annihilation_commutator (k : Ch01.Band L) :
    A02.commutator (shiftedHamiltonian L) (momentumAnnihilation L k) =
      (-k.val : ℂ) • momentumAnnihilation L k := by sorry

lemma sea_ket_ne_zero : seaKet L ≠ 0 := by sorry

lemma bare_hamiltonian_sea :
    bareHamiltonian L (seaKet L) = (seaEnergy L : ℂ) • seaKet L := by sorry

lemma shifted_hamiltonian_sea : shiftedHamiltonian L (seaKet L) = 0 := by sorry

end Energy

/-- These physical contracts use exactly the notes' positive-even lattice. -/
lemma sea_card_even (h : ℕ) (hh : 0 < h) : (seaConfiguration (2*h)).card = h := by sorry

lemma sea_energy_even (h : ℕ) (hh : 0 < h) :
    seaEnergy (2*h) = -((h : ℤ) * ((h : ℤ) - 1) / 2) := by sorry

lemma sea_energy_negative (h : ℕ) (hh : 2 ≤ h) : seaEnergy (2*h) < 0 := by sorry

lemma bare_sea_action_ne_zero (h : ℕ) (hh : 2 ≤ h) :
    bareHamiltonian (2*h) (seaKet (2*h)) ≠ 0 := by sorry

lemma sea_energy_half_size_one : seaEnergy 2 = 0 := by sorry

end Bosonize.Ch05
```
