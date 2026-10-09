# Chapter 3 lab notebook: Finite Fourier transform

Status (2026-10-09): **Phase A compiled, unlocked, awaiting human interface review.** Twelve complete definitions/abbreviations and 31 unproved lemma stubs. Namespace: `Bosonize.Ch03`. Source: [Chapter 3](../../../notes/md/ch03_fourier.md), with [A01](../../../notes/appendices/a01_fourier_scalars_and_characters.md). Lean module: `BosonizeStubs/Ch03Fourier.lean`.

## Complete definitions and typed directions

| Object | Source → target / meaning |
| --- | --- |
| `analysis L ζ` (S) | `(Ch01.Lattice L → K) →ₗ[K] (Ch01.Band L → K)`; negative-sign finite-sum kernel. |
| `synthesis L ζ` (T) | `(Ch01.Band L → K) →ₗ[K] (Ch01.Lattice L → K)`; positive-sign kernel. |
| `inverseAnalysis L ζ` | Same direction as T, scaled by `(L:K)⁻¹`; its inverse claims require nonzero scalar L. |
| `PositionSpace`, `MomentumSpace` | Euclidean spaces over ℂ on the frozen position and signed-band index types. |
| `positionFunctions`, `momentumFunctions` | `WithLp.linearEquiv` from each Euclidean carrier to ordinary functions. |
| `analysisEuclidean`, `synthesisEuclidean` | Canonical-root S/T conjugated by the two distinct function equivalences. |
| `unitaryFourier`, `inverseUnitaryFourier` | `(normalization L : ℂ)` times the transported S/T, in their respective directions. Their names identify intended contracts, not proved properties. |
| `transportPositionOperator` | Conjugation of an existing Chapter 2 function operator onto the spatial Euclidean carrier. |

S/T are constructed from the displayed finite sums. Structural additivity and scalar-linearity fields are complete elementary proofs; no theorem stub is used to manufacture a definition. `inverseAnalysis` is a specified candidate until the two inverse statements are proved. All generic kernel claims require a primitive root, and inverse/bijectivity additionally require `(L:K) ≠ 0`.

The complex transform is initially a linear map. No `LinearEquiv` or `LinearIsometryEquiv` containing unproved project proof fields is defined. After Phase B, bundling those completed inverse/isometry contracts is a further reviewed declaration addition if desired; the lock must not be extended silently.

## Mathlib reuse and sign orientation

The installed `ZMod.dft` is an unscaled negative-sign linear equivalence and its `.symm` has a positive-sign kernel multiplied by 1/L. `analysis_eq_dft` is the exact forward bridge at `bandProjection k`; `inverse_analysis_eq_inv_dft` specifies the inverse bridge after reindexing a band function through `A01.bandEquiv.symm`. These are unproved bridge stubs. Once proved, Phase B can reuse Mathlib inversion rather than duplicating it. The explicit generic finite-sum maps remain useful for arbitrary primitive roots; trigonometric dispersion is asserted only for the selected canonical complex root.

`WithLp.linearEquiv 2 ℂ (I → ℂ)` runs from `EuclideanSpace ℂ I` to functions. Transport uses e_target.symm ∘ map ∘ e_source. No isometry assertion is made for the default ordinary-function norm. The counting inner products and finite-dimensional `LinearMap.adjoint` are applied on the Euclidean carriers.

## Proposed proof dependency order

1. Finish A01 root/representative, character-law, sum-transport and orthogonality obligations.
2. Establish finite-sum evaluation and the delta-at-zero image. Expand or reuse the DFT bridge to prove both compositions equal L times the identity. Divide only with the stated scalar-nonzero hypothesis; deduce bijectivity.
3. Establish shift and inverse-shift eigenvectors, then the forward/backward differences and algebraic Laplacian. Prove the transformed operator identities by periodic reindexing or the invertible character expansion. The positive-sign eigenvector and negative-sign analysis conventions give ζ^k−1 for forward difference.
4. Transport S/T compositions to Euclidean carriers, use complex conjugation to prove `analysisEuclidean.adjoint = synthesisEuclidean`, then apply A01's real normalization.
5. Prove normalized left/right inverses, adjoint, inner-product preservation, isometry and surjectivity. Surjectivity is a separate target, not inferred solely from isometry.
6. Connect the transported frozen Laplacian to momentum multiplication. Evaluate the canonical-root algebraic eigenvalue as −4 sin²(πk/L), with integer k and explicit nonzero L.
7. Check singleton and even-Nyquist contracts throughout. No assumption that every nonzero frequency is coprime to L is allowed.

The delta-at-zero image is a nonzero transform witness obligation; all character values have A01 nonzero/norm contracts. L=1 yields a single evaluation and an empty nontrivial-frequency branch. For even L, +L/2 is the retained endpoint and its transported negative is itself. No physical half-filling, CAR model, analytic limit or energy-budget margin is introduced here.

## Review choices and future obligations

Adopt the source's separate algebraic and Hilbert layers, frozen Chapter 2 operators, exact kernel signs and normalization. Adapt reuse to explicit bridge lemmas instead of silently identifying Band with ZMod. Reject T as an unscaled inverse, 1/L normalization on both physical kernels, the retired fractional-power dispersion expression and suppressed warnings.

The Chapter 3-specific proof suggestions directory has no matching file; the [revised stub guide](../../../docs/stub_suggestion/chapter_3_fourier_stub_draft.md), A01 and current inline strategies are advisory. All proposed bridge, inverse, adjoint and eigenvalue statements still need proof. If proof development discovers a shared mathematical/interface failure, checkpoint it and follow the adaptive issue-sprint procedure; do not change existing Core.

Review the size of the generic field interface, the proposed helper names, the inverse scalar assumption, and whether future bundling should be proposed after the current proofs. Definitions and statements can still be revised during this unlocked review.

## Validation and review gate

The installed compiler is `leanprover/lean4:v4.35.0-rc4`, with the dependency versions in `lake-manifest.json`. Native Lean MCP tools are not exposed in this chat; validation uses the installed compiler and local Mathlib sources. This is compiler evidence, not MCP/LSP evidence.

- `lake build Bosonize` and `lake build BosonizeStubs` pass.
- Fresh `lake env lean` compilation of A01 and Chapter 3 passes, producing respectively 30 and 31 expected `declaration uses sorry` diagnostics and no other diagnostics.
- Structural inspection checks exactly one `:= by sorry` in each lemma, no definition placeholders and exact notebook/source equality.
- Fresh `#print axioms` probes cover all 18 definitions/abbreviations across both modules. Dependencies contain only subsets of `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. Definitions do not depend on the new unproved lemmas. This audit is not a proof of the 61 theorem statements.
- All 69 existing guard tests pass. The non-strict statement guard against the pre-draft committed baseline verifies 52 existing statements and 54 existing commands, reporting only the two new unlocked files. The complete Core source guard passes against the same baseline.
- `make ci` intentionally fails at its strict statement guard on those two unreviewed additions. No lock was generated or accepted, and no guard, Core source or toolchain was changed to hide that result.

Phase A is complete only as a compiled proposal. Review definitions, hypotheses, theorem signatures, kernel orientation, representative convention and downstream usefulness before approving a strict lock. Phase B and Core promotion have not started. Full CI can pass after the approved new interface enters the lock through the ordinary review workflow.

## Provenance

Source baseline before this draft: `6ec5df254fb130a1a1483ceddffdaf22ee3e0d06`. The following hashes identify the exact source material consulted. These are source snapshots, not mathematical certification. Existing dated reviews may describe earlier revisions; the current notes and completion ledger control this draft.

| Source | SHA-256 |
| --- | --- |
| `notes/md/ch03_fourier.md` | `d4da4a800d18e68580fb793a3c8c9ba55d54836cf06253dd69e26ac86b89370e` |
| `notes/appendices/a01_fourier_scalars_and_characters.md` | `0b65cf6f5ed73a59ef5d25b2b502c34c4315cb5ce1df67cb690c3defba70b165` |
| `docs/stub_suggestion/chapter_3_fourier_stub_draft.md` | `793284489dbe77f76ca1a781fea878e2080445aba9375f72ae529c28d4dbe9a1` |
| `note/proof_suggestions_revision_2026-10-09.md` | `1db5f28b3e392d3b400ccc219ac640778fc5ceabc5cba17dfeb44b225a1b383c` |
| `note/notes_review_completion_2026-10-09.md` | `ee96609b0c32346be604041a99e3345c3420b71c830c88ef83ff8d93bd9c1dc1` |
| `Bosonize/Core/Ch01LatticeBand.lean` | `a88cd251573aa8a5416afa583b0a97b1e575ab09d4742b13a5b0be0e8a16b132` |
| `Bosonize/Core/Ch02UmbralCalculus.lean` | `d8d70d75372733aefda49e50baa033aaa5b363a57c0ec67a5a91368ac2d6f425` |
| `lean-toolchain` | `8f89aa44fccdb1a0b6cc768c7c9f54b94cd40e47a08d582f82d1235f13075cf7` |
| `lake-manifest.json` | `237acfc7835876d993b4025c88431d8d39f76db83cab94c9f9a640395f9c61f4` |


## Exact Lean source snapshot

This block is byte-for-byte identical to the corresponding Lean file, including its final newline. It is the complete reviewable interface and includes the structural proofs needed to construct linear maps; every lemma remains a one-sorry stub.

Module SHA-256: `1803d9a61f2950734dc836796b0e4d910b0dea1feb6894fca6e15d8f1033e7fd`.

```lean
module

public import Bosonize.Core.Ch02UmbralCalculus
public import BosonizeStubs.A01FourierCharacters
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Chapter 3: finite Fourier transform

Phase A, unlocked. S is negative-sign analysis; T is positive-sign synthesis.
The generic algebraic inverse is L⁻¹ T. Complex counting-space normalization is separate.
No isometry equivalence is bundled until its proof fields are available in Phase B.
-/

@[expose] public section

namespace Bosonize.Ch03

open scoped BigOperators

variable {K : Type*} [Field K]

/-- Unscaled negative-sign analysis on distinct position and band function carriers. -/
noncomputable def analysis (L : ℕ) [NeZero L] (ζ : K) :
    (Ch01.Lattice L → K) →ₗ[K] (Ch01.Band L → K) where
  toFun f k := ∑ x : Ch01.Lattice L, f x * A01.integerCharacter ζ (-k.val) (x.val : ℤ)
  map_add' f g := by
    funext k
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]

/-- Unscaled positive-sign synthesis, before division by L. -/
noncomputable def synthesis (L : ℕ) [NeZero L] (ζ : K) :
    (Ch01.Band L → K) →ₗ[K] (Ch01.Lattice L → K) where
  toFun g x := ∑ k : Ch01.Band L, g k * A01.bandCharacter L ζ k x
  map_add' f g := by
    funext x
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]

/-- Candidate algebraic inverse; inverse claims explicitly require nonzero scalar L. -/
noncomputable def inverseAnalysis (L : ℕ) [NeZero L] (ζ : K) :
    (Ch01.Band L → K) →ₗ[K] (Ch01.Lattice L → K) := (L : K)⁻¹ • synthesis L ζ

lemma analysis_apply (L : ℕ) [NeZero L] (ζ : K) (f : Ch01.Lattice L → K)
    (k : Ch01.Band L) : analysis L ζ f k =
      ∑ x : Ch01.Lattice L, f x * A01.integerCharacter ζ (-k.val) (x.val : ℤ) := by sorry

lemma synthesis_apply (L : ℕ) [NeZero L] (ζ : K) (g : Ch01.Band L → K)
    (x : Ch01.Lattice L) : synthesis L ζ g x =
      ∑ k : Ch01.Band L, g k * A01.bandCharacter L ζ k x := by sorry

lemma synthesis_analysis (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) :
    (synthesis L ζ).comp (analysis L ζ) = (L : K) • LinearMap.id := by sorry

lemma analysis_synthesis (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) :
    (analysis L ζ).comp (synthesis L ζ) = (L : K) • LinearMap.id := by sorry

lemma inverse_analysis_left (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (hLK : (L : K) ≠ 0) :
    (inverseAnalysis L ζ).comp (analysis L ζ) = LinearMap.id := by sorry

lemma inverse_analysis_right (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (hLK : (L : K) ≠ 0) :
    (analysis L ζ).comp (inverseAnalysis L ζ) = LinearMap.id := by sorry

lemma analysis_bijective (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (hLK : (L : K) ≠ 0) :
    Function.Bijective (analysis L ζ) := by sorry

/-- A nonzero image witness: the position delta at zero analyzes to the constant one. -/
lemma analysis_delta_zero (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) :
    analysis L ζ (Pi.single (0 : Ch01.Lattice L) 1) = fun _ ↦ 1 := by sorry

lemma shift_character (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) :
    Ch02.shift (A01.bandCharacter L ζ k) = (ζ ^ k.val) • A01.bandCharacter L ζ k := by sorry

lemma inverse_shift_character (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) :
    Ch02.inverseShift (A01.bandCharacter L ζ k) =
      (ζ ^ (-k.val)) • A01.bandCharacter L ζ k := by sorry

lemma forward_diff_character (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) :
    Ch02.forwardDiff (A01.bandCharacter L ζ k) =
      (ζ ^ k.val - 1) • A01.bandCharacter L ζ k := by sorry

lemma backward_diff_character (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) :
    Ch02.backwardDiff (A01.bandCharacter L ζ k) =
      (1 - ζ ^ (-k.val)) • A01.bandCharacter L ζ k := by sorry

lemma laplacian_eigenvalue_factor (ζ : K) (hζ : ζ ≠ 0) (k : ℤ) :
    (ζ ^ k - 1) * (1 - ζ ^ (-k)) = ζ ^ k + ζ ^ (-k) - 2 := by sorry

lemma laplacian_character (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) :
    Ch02.laplacian (A01.bandCharacter L ζ k) =
      (ζ ^ k.val + ζ ^ (-k.val) - 2) • A01.bandCharacter L ζ k := by sorry

lemma analysis_forward_diff (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (f : Ch01.Lattice L → K) (k : Ch01.Band L) :
    analysis L ζ (Ch02.forwardDiff f) k = (ζ ^ k.val - 1) * analysis L ζ f k := by sorry

lemma analysis_backward_diff (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (f : Ch01.Lattice L → K) (k : Ch01.Band L) :
    analysis L ζ (Ch02.backwardDiff f) k = (1 - ζ ^ (-k.val)) * analysis L ζ f k := by sorry

lemma analysis_laplacian (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (f : Ch01.Lattice L → K) (k : Ch01.Band L) :
    analysis L ζ (Ch02.laplacian f) k =
      (ζ ^ k.val + ζ ^ (-k.val) - 2) * analysis L ζ f k := by sorry

/-- Counting-inner-product spatial carrier. -/
abbrev PositionSpace (L : ℕ) := EuclideanSpace ℂ (Ch01.Lattice L)

/-- Counting-inner-product signed momentum carrier. -/
abbrev MomentumSpace (L : ℕ) := EuclideanSpace ℂ (Ch01.Band L)

/-- Euclidean-to-function transport; this does not assert a function-norm isometry. -/
noncomputable def positionFunctions (L : ℕ) : PositionSpace L ≃ₗ[ℂ] (Ch01.Lattice L → ℂ) :=
  WithLp.linearEquiv 2 ℂ (Ch01.Lattice L → ℂ)

noncomputable def momentumFunctions (L : ℕ) : MomentumSpace L ≃ₗ[ℂ] (Ch01.Band L → ℂ) :=
  WithLp.linearEquiv 2 ℂ (Ch01.Band L → ℂ)

/-- Canonical unscaled analysis transported to the counting-space carriers. -/
noncomputable def analysisEuclidean (L : ℕ) [NeZero L] : PositionSpace L →ₗ[ℂ] MomentumSpace L :=
  (momentumFunctions L).symm.toLinearMap.comp
    ((analysis L (A01.canonicalRoot L)).comp (positionFunctions L).toLinearMap)

noncomputable def synthesisEuclidean (L : ℕ) [NeZero L] : MomentumSpace L →ₗ[ℂ] PositionSpace L :=
  (positionFunctions L).symm.toLinearMap.comp
    ((synthesis L (A01.canonicalRoot L)).comp (momentumFunctions L).toLinearMap)

/-- Normalized U remains a linear map in Phase A. -/
noncomputable def unitaryFourier (L : ℕ) [NeZero L] : PositionSpace L →ₗ[ℂ] MomentumSpace L :=
  (A01.normalization L : ℂ) • analysisEuclidean L

/-- Positive-sign candidate normalized inverse. -/
noncomputable def inverseUnitaryFourier (L : ℕ) [NeZero L] : MomentumSpace L →ₗ[ℂ] PositionSpace L :=
  (A01.normalization L : ℂ) • synthesisEuclidean L

/-- Transport a frozen Chapter 2 operator without redefining it. -/
noncomputable def transportPositionOperator (L : ℕ)
    (A : Module.End ℂ (Ch01.Lattice L → ℂ)) : Module.End ℂ (PositionSpace L) :=
  (positionFunctions L).symm.toLinearMap.comp (A.comp (positionFunctions L).toLinearMap)

lemma analysis_eq_dft (L : ℕ) [NeZero L] (f : Ch01.Lattice L → ℂ) (k : Ch01.Band L) :
    analysis L (A01.canonicalRoot L) f k =
      ZMod.dft f (Ch01.bandProjection L k) := by sorry

lemma inverse_analysis_eq_inv_dft (L : ℕ) [NeZero L] (g : Ch01.Band L → ℂ)
    (x : Ch01.Lattice L) :
    inverseAnalysis L (A01.canonicalRoot L) g x =
      (ZMod.dft.symm (fun r ↦ g ((A01.bandEquiv L).symm r))) x := by sorry

lemma synthesisEuclidean_analysisEuclidean (L : ℕ) [NeZero L] :
    (synthesisEuclidean L).comp (analysisEuclidean L) = (L : ℂ) • LinearMap.id := by sorry

lemma analysisEuclidean_synthesisEuclidean (L : ℕ) [NeZero L] :
    (analysisEuclidean L).comp (synthesisEuclidean L) = (L : ℂ) • LinearMap.id := by sorry

lemma analysisEuclidean_adjoint (L : ℕ) [NeZero L] :
    (analysisEuclidean L).adjoint = synthesisEuclidean L := by sorry

lemma unitary_inverse_left (L : ℕ) [NeZero L] :
    (inverseUnitaryFourier L).comp (unitaryFourier L) = LinearMap.id := by sorry

lemma unitary_inverse_right (L : ℕ) [NeZero L] :
    (unitaryFourier L).comp (inverseUnitaryFourier L) = LinearMap.id := by sorry

lemma unitary_adjoint (L : ℕ) [NeZero L] :
    (unitaryFourier L).adjoint = inverseUnitaryFourier L := by sorry

lemma unitary_inner (L : ℕ) [NeZero L] (f g : PositionSpace L) :
    inner ℂ (unitaryFourier L f) (unitaryFourier L g) = inner ℂ f g := by sorry

lemma unitary_isometry (L : ℕ) [NeZero L] : Isometry (unitaryFourier L) := by sorry

lemma unitary_surjective (L : ℕ) [NeZero L] :
    Function.Surjective (unitaryFourier L) := by sorry

lemma unitary_laplacian (L : ℕ) [NeZero L] (f : PositionSpace L) (k : Ch01.Band L) :
    momentumFunctions L
      (unitaryFourier L (transportPositionOperator L Ch02.laplacian f)) k =
      (A01.canonicalRoot L ^ k.val + A01.canonicalRoot L ^ (-k.val) - 2) *
        momentumFunctions L (unitaryFourier L f) k := by sorry

lemma canonical_laplacian_dispersion (L : ℕ) [NeZero L] (k : ℤ) :
    A01.canonicalRoot L ^ k + A01.canonicalRoot L ^ (-k) - 2 =
      ((-4 * Real.sin (Real.pi * (k : ℝ) / (L : ℝ)) ^ 2 : ℝ) : ℂ) := by sorry

lemma singleton_analysis (f : Ch01.Lattice 1 → ℂ) (k : Ch01.Band 1) :
    analysis 1 (A01.canonicalRoot 1) f k = f 0 := by sorry

end Bosonize.Ch03
```
