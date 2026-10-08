# Chapter 1 lab notebook: Lattice and band geometry

Status: the current 20 lemma signatures match the recorded lock baseline (checked 2026-10-08). The lemma bodies remain placeholders; Phase B has not started. The v2 guard also freezes definitions and surrounding non-lemma context; strict checks pass against the approved baseline.

Source: `notes/md/ch01_lattice_band_geometry.md`, definitions 1.1–1.3 and lemma 1.4, equations (1.1)–(1.10). The master index `notes/md/TOC.md` identifies lattice geometry as chapter 1, umbral calculus as chapter 2, and Fourier transforms as chapter 3.

## Representation and rationale

The namespace is `Bosonize.Ch01`. `Lattice L` is Mathlib's `ZMod L`, the additive quotient of integers modulo `L`. `L` is a natural number, and geometric operations and claims explicitly require `hL : 0 < L`. In particular, `ZMod 0` is not treated as a finite spatial lattice.

`Band L` is the subtype of signed integers satisfying exactly `-(L : ℤ) < 2*k ∧ 2*k ≤ (L : ℤ)`. This preserves the source's signed momentum labels and its strict lower and inclusive upper bounds, with no global evenness assumption. `bandFinset` filters the finite integer interval `[-L,L]` by this predicate. A fully proved `Fintype` instance makes finite sums available to subsequent chapters; its membership proof uses only integer arithmetic. Both the enumeration and subtype are computable.

`quotientMap` is integer casting into `ZMod L`; `bandProjection` restricts it to the band. For `representative`, take the standard residue `a = x.val` with `0 ≤ a < L`. Return `a` if `2*a ≤ L`, and `a-L` otherwise. The subtype bounds are proved inside the definition using `omega` and Mathlib's `ZMod.val_lt`. There is no use of a staged theorem or choice of an unproved inverse to construct this function.

`bandAdd` and `bandNeg` apply this concrete representative to addition and negation in `ZMod L`, exactly as in equations (1.5) and (1.6). `zeroMomentum` is a concrete band element for every positive `L`; its membership proof is complete and witnesses nonemptiness independently of all theorem stubs.

No `Equiv` or `AddCommGroup` instance is installed in Phase A: constructing these via the staged inverse identities would make their definitions depend on placeholder proofs. The inverse and additive-law signatures expose the proposed interface for review. Physical scaling by `2π/L` is contextual in this chapter; these definitions concern integer labels and quotient arithmetic and do not introduce real or complex momentum values.

## Source coverage and edge cases

| Source | Lean declarations | Interpretation |
| --- | --- | --- |
| (1.1) | `Lattice` | Spatial quotient `ZMod L` |
| (1.2) | `inBandPredicate`, `Band`, `bandFinset` | Exact centered integer band |
| (1.3) | `quotientMap`, `bandProjection` | Quotient projection and restriction |
| (1.4) | `representative`, `projection_representative` | Concrete representative and section identity |
| (1.5), (1.6) | `bandAdd`, `bandNeg` | Arithmetic transported through the quotient |
| (1.7) | `card_band_finset`, `card_band` | Cardinality of both enumerated and typed band |
| Lemma 1.4(2) | `representative_projection`, `band_projection_bijective`, `representative_unique` | Both inverse identities, bijectivity, and uniqueness |
| (1.8) | `band_add_wrap` | Unique wrapping integer with `-1 ≤ w ≤ 1` |
| (1.9) | `nyquist_neg` | Positive even Nyquist endpoint is self-inverse |
| (1.10) | `band_neg_of_ne_nyquist` | Away from that endpoint, integer labels negate normally |

The wrapping multiplier is an integer; `-1 ≤ w ≤ 1` is exactly membership in `{-1,0,1}`. `∃!` asserts uniqueness for the entire bounded equation predicate. The equation keeps the source's sign: wrapped sum equals ordinary sum minus `w*L`.

For even positive `L`, `even_band_bounds` states the interval `[-L/2+1,L/2]`. `nyquist_neg` takes a band element whose integer value is `L/2`; existence of that label follows from the proposed interval characterization. The exceptional-mode hypothesis is explicit on `band_neg_of_ne_nyquist`. This is an equality of integer labels, since `-k.val` must be shown to lie in the band before it can be used as a band element.

For odd `L`, `odd_band_neg` records the symmetric band's ordinary negation. `singleton_band` handles `L=1`, where the only momentum is zero. At `L=2` the labels are `0,1`, and the Nyquist label `1` negates to itself. At `L=4` the labels are `-1,0,1,2`; at `L=3` they are `-1,0,1`. These are explanatory examples of the definitions, not additional proved theorems.

The additive-law, projection-compatibility, odd-negation, singleton, membership, and zero-witness theorem signatures are supporting interfaces in addition to the explicitly numbered source claims. There are no energy or Fermi-sea margins in this chapter. Evenness is required only on the even-band and Nyquist statements; the source's requirement from chapter 6 onward is not imposed on this foundational chapter.

## Validation and review boundary

Lean MCP tools are not exposed in this session. Validation uses the installed project's `lake`/Lean compiler; Mathlib identifiers are checked against local library sources. No remote search or extra tooling installation is needed.

`lake build Bosonize` passed, and `lake build BosonizeStubs` passed with only the 20 expected placeholder warnings. The existing Core aggregator remains in legacy format, so the staging aggregator retains that format as well. The new chapter uses Lean 4.35's module system with public, exposed declarations.

All 20 lemma declarations deliberately end in exactly `:= by sorry`. Definitions and instances contain no placeholders. This is signature elaboration and definition validation, not completion of the chapter's proofs. The staging aggregator imports the chapter so `lake build BosonizeStubs` checks it routinely. No source note or Core module is modified.

The review should confirm the exact band bounds, the concrete representative convention, the wrapping equation, the explicit positivity and evenness hypotheses, and whether the supporting interfaces should be retained. Phase B proof search and signature locking await approval, as required by `.agents/workflows/start_chapter.md` step 4 and `.agents/skills/formalizer/SKILL.md` Phase A.

## Freeze and suggestion review (2026-10-08)

`python3 scripts/guards/stub_lock.py --check` passes for all 20 current lemma signatures, including the rename from `inBand` to `inBandPredicate` and the switch from `theorem` to `lemma`. The current staging build passes with the expected 20 placeholder warnings. The saved manifest is left unchanged. The initial v1 audit found definition and context gaps. The subsequent v2 audit verifies 20 lemma headers and 24 frozen command entries. Its 59-test suite and 15 actual-chapter temporary-copy checks pass; strict mode rejects definition, instance, namespace, import, claim, and addition changes. CI now runs guard tests and strict verification before the Lean builds. See `docs/spec/freeze_audit.md` for the evidence and limits. The baselines and Lean source were preserved; future proof work must pass strict verification and source/dependency review.

The chapter-specific proof suggestion is `docs/proof_suggestion/Ch01LatticeBand_GeminiPro.md`. Its dependency plan is useful: basic integer bounds; the two quotient/representative inverse identities; projection compatibility and transported group laws; then cardinality, wrap, and Nyquist cases. This plan is a candidate for Phase B, not a set of accepted proofs.

Compiling an unchanged temporary Lean copy of this suggestion with the current project toolchain exits with errors. Examples include the wrong arguments to `ZMod.val_natCast` (suggestion line 107), missing `NeZero L` (line 118) and finite-lattice instance (line 203), invalid dependent rewrites (line 137), incorrect reliance on `rfl` for projection of zero (lines 185 and 192), and a failed definitional equality between finset cardinality and subtype cardinality (line 208). No suggested proof was copied into the staging file. Any later helper or tactic must be verified for the actual locked interface, with explicit positivity instances where needed.

The available stub suggestion, `docs/stub_suggestion/chapter_2_umbral_calculus_core.md`, concerns chapter 2 rather than this chapter. It is advisory material for a future chapter-2 drafting task. Static review finds unfinished definitions `umbralMap` and `polyForwardDiff`, which violate the complete-definition contract, and an unrestricted `L` in `sum_by_parts`, which does not supply the positive-size condition/instance needed for a finite `ZMod L` sum. Future drafting must also evaluate whether the suggested raw function operators sufficiently expose the source's linear-endomorphism interfaces. The chapter-2 suggestion was not compiler-validated or adopted during this chapter-1 audit.

## Exact draft declarations

The following snapshot mirrors the Lean source, including complete definitions and placeholder theorem bodies.

```lean
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
# Chapter 1: Lattice and band geometry

Phase A interface, following `notes/md/ch01_lattice_band_geometry.md`.
Definitions are complete; lemma bodies are intentionally staged for review.
The positive boundary is included and the negative boundary is excluded.
-/

@[expose] public section

namespace Bosonize.Ch01

/-- The periodic spatial lattice. All geometric claims require `0 < L`. -/
abbrev Lattice (L : ℕ) := ZMod L

/-- The predicate for centered-band. -/
def inBandPredicate (L : ℕ) (k : ℤ) : Prop := -(L : ℤ) < 2 * k ∧ 2 * k ≤ (L : ℤ)

instance (L : ℕ) (k : ℤ) : Decidable (inBandPredicate L k) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Band subtype. Actual signed integer labels. -/
abbrev Band (L : ℕ) := {k : ℤ // inBandPredicate L k}

/-- A computable enumeration of the exact band, without a parity assumption. -/
def bandFinset (L : ℕ) : Finset ℤ :=
  (Finset.Icc (-(L : ℤ)) (L : ℤ)).filter (inBandPredicate L)

instance (L : ℕ) : Fintype (Band L) :=
  Fintype.ofFinset (bandFinset L) (by
    intro k
    change k ∈ bandFinset L ↔ inBandPredicate L k
    simp only [bandFinset, Finset.mem_filter, Finset.mem_Icc]
    unfold inBandPredicate
    omega)

/-- The canonical quotient projection. -/
def quotientMap (L : ℕ) (k : ℤ) : Lattice L := (k : ZMod L)

/-- The quotient projection restricted to the band. -/
def bandProjection (L : ℕ) (k : Band L) : Lattice L := quotientMap L k.val

/-- Center the standard residue in `[0,L)` at the positive Nyquist endpoint. -/
def representative (L : ℕ) (hL : 0 < L) (x : Lattice L) : Band L := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  have hx := ZMod.val_lt x
  exact if h : 2 * (x.val : ℤ) ≤ (L : ℤ) then
    ⟨(x.val : ℤ), by unfold inBandPredicate; omega⟩
  else
    ⟨(x.val : ℤ) - (L : ℤ), by unfold inBandPredicate; omega⟩

/-- Transported band addition, equation (1.5). -/
def bandAdd (L : ℕ) (hL : 0 < L) (k p : Band L) : Band L :=
  representative L hL (bandProjection L k + bandProjection L p)

/-- Transported band negation, equation (1.6). -/
def bandNeg (L : ℕ) (hL : 0 < L) (k : Band L) : Band L :=
  representative L hL (-bandProjection L k)

/-- A concrete zero momentum witnesses that every positive-size band is inhabited. -/
def zeroMomentum (L : ℕ) (hL : 0 < L) : Band L :=
  ⟨0, by unfold inBandPredicate; omega⟩

lemma mem_band_finset (L : ℕ) (k : ℤ) :
    k ∈ bandFinset L ↔ inBandPredicate L k := by sorry

lemma zero_mem_band (L : ℕ) (hL : 0 < L) : inBandPredicate L 0 := by sorry

lemma card_band_finset (L : ℕ) (hL : 0 < L) :
    (bandFinset L).card = L := by sorry

lemma card_band (L : ℕ) (hL : 0 < L) :
    Fintype.card (Band L) = L := by sorry

/-- First inverse identity, including the section condition in equation (1.4). -/
lemma projection_representative (L : ℕ) (hL : 0 < L) (x : Lattice L) :
    bandProjection L (representative L hL x) = x := by sorry

/-- Second inverse identity establishes uniqueness of the centered representative. -/
lemma representative_projection (L : ℕ) (hL : 0 < L) (k : Band L) :
    representative L hL (bandProjection L k) = k := by sorry

lemma band_projection_bijective (L : ℕ) (hL : 0 < L) :
    Function.Bijective (bandProjection L) := by sorry

lemma representative_unique (L : ℕ) (hL : 0 < L) (x : Lattice L) (k : Band L)
    (hk : bandProjection L k = x) : k = representative L hL x := by sorry

/-- The wrapping integer lies in `{-1,0,1}` and is unique with this property. -/
lemma band_add_wrap (L : ℕ) (hL : 0 < L) (k p : Band L) :
    ∃! w : ℤ, (-1 ≤ w ∧ w ≤ 1) ∧
      (bandAdd L hL k p).val = k.val + p.val - w * (L : ℤ) := by sorry

lemma band_add_projection (L : ℕ) (hL : 0 < L) (k p : Band L) :
    bandProjection L (bandAdd L hL k p) =
      bandProjection L k + bandProjection L p := by sorry

lemma band_neg_projection (L : ℕ) (hL : 0 < L) (k : Band L) :
    bandProjection L (bandNeg L hL k) = -bandProjection L k := by sorry

lemma band_add_assoc (L : ℕ) (hL : 0 < L) (k p q : Band L) :
    bandAdd L hL (bandAdd L hL k p) q = bandAdd L hL k (bandAdd L hL p q) := by sorry

lemma band_add_comm (L : ℕ) (hL : 0 < L) (k p : Band L) :
    bandAdd L hL k p = bandAdd L hL p k := by sorry

lemma band_zero_add (L : ℕ) (hL : 0 < L) (k : Band L) :
    bandAdd L hL (zeroMomentum L hL) k = k := by sorry

lemma band_neg_add_cancel (L : ℕ) (hL : 0 < L) (k : Band L) :
    bandAdd L hL (bandNeg L hL k) k = zeroMomentum L hL := by sorry

/-- The even-size interval includes the positive endpoint and omits the negative one. -/
lemma even_band_bounds (L : ℕ) (hL : 0 < L) (hEven : Even L) (k : ℤ) :
    inBandPredicate L k ↔ -((L / 2 : ℕ) : ℤ) + 1 ≤ k ∧ k ≤ ((L / 2 : ℕ) : ℤ) := by sorry

/-- Equation (1.9), stated for a band element with the Nyquist integer label. -/
lemma nyquist_neg (L : ℕ) (hL : 0 < L) (hEven : Even L) (k : Band L)
    (hk : k.val = ((L / 2 : ℕ) : ℤ)) : bandNeg L hL k = k := by sorry

/-- Equation (1.10): ordinary integer negation away from the even Nyquist mode. -/
lemma band_neg_of_ne_nyquist (L : ℕ) (hL : 0 < L) (hEven : Even L)
    (k : Band L) (hk : k.val ≠ ((L / 2 : ℕ) : ℤ)) :
    (bandNeg L hL k).val = -k.val := by sorry

lemma odd_band_neg (L : ℕ) (hL : 0 < L) (hOdd : Odd L) (k : Band L) :
    (bandNeg L hL k).val = -k.val := by sorry

/-- At `L = 1`, the entire band consists of zero. -/
lemma singleton_band (k : Band 1) : k.val = 0 := by sorry

end Bosonize.Ch01

```
