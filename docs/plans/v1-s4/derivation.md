# V1-S4 derivation: finite current words

## Scope and source reconciliation

S4 compares actual nonwrapping finite CAR density currents in a free sea with
the existing A08 oscillator functional. It does not construct an interacting
state. S1 is the oscillator word/Wick foundation; S2 and S3 are not needed for
this bridge.

The conventions are fixed by the current sources. A08 uses
`OscGen M = Bool × (Orientation × Fin M)`. `true` is multiplication by `X`
(creation); `false` is the weighted derivative
`(i.val+1) * pderiv` (annihilation). A07 identifies the opposite orientation
by `oppositeOrientation`. CH09 defines raw `rho h m` as `dGamma (shift (2*h)
m)`, where a matrix entry transports source momentum `k` to target `k+m`;
positive transfer creates a particle-hole excitation and negative transfer
lowers it. A05 lifts this current to the actual species-tagged fermion carrier.
Thus the finite dictionary is

* `true, (nu,i)` ↦ `A05.rho h nu +(i.val+1)`;
* `false, (nu,i)` ↦ `A05.rho h nu -(i.val+1)`.

There is no square-root factor or sign reversal. At transfer zero the raw
current is total number; the neutral sea-normal-ordered current is the relative
charge. S4 uses nonzero positive mode labels, so its generators use raw
currents without a zero-mode sea subtraction. The map extends by `FreeAlgebra`
to all words, preserving displayed multiplication order. This homomorphism is
not a representation of the oscillator CCR quotient globally.

## Exact action margin

In a displayed word `g₁ … gᵣ`, `gᵣ` acts first. For a path and each finite
species `ν`, let `E_{ν,j}` be the oscillator energy after the first `j`
rightmost actions; creation adds `m`, annihilation subtracts `m`, with
`m=i.val+1`. Energies are species-resolved, so positive energy in one species
cannot mask a negative intermediate energy in another. A live path has
`E_{ν,j} ≥ 0` for both active species at every prefix. If a lowering step has
`m>E_{ν,j}`, that branch is killed at that step. The certificate still
requires the source margin `m+Eν+|Nν|≤h` to invoke the actual finite-current
action identity; after both actions are shown zero, later factors need no
margin on that branch.

For a live annihilator of weight `m` acting on a homogeneous state of energy
`Eν`, the pull-through through a positive-current partition word uses CH10's
signed two-mode commutator at each remaining factor. For a factor of weight
`n` and remaining positive energy `Rν`, the exact premise is
`m+n+Rν+|Nν| ≤ h`; since `n+Rν=Eν`, this is exactly
`m+Eν+|Nν| ≤ h`. It follows the actual species-resolved suffix rather than
just the final energy.

For a word with mixed signs, each generator expands into two
oriented/sign choices. The actual product coefficient is recorded for every
branch; path conditions apply only to nonzero-coefficient branches. This
handles zero squeeze, where flipped branches have zero coefficient. Each
surviving branch has a recursive certificate for species-resolved live
prefixes, local margins, the mode-energy budget, or a first killed step. This
condition is numerical and independent of the target intertwining or moment.
The convenient uniform wrapper for word length `d`, maximum mode weight `M`, and charges
`Nν` is `2*d*M+|Nν| ≤ h`: given a live path, each prefix energy is at most
`d*M`, each mode weight at most `M`, and the Haldane/Gram domain needs
`2*d*M+|Nν|≤h`. The proved `uniform_margin_path` theorem derives the complete path condition
with `K=d*M` for every word of length at most `d`; `inverse_branches_length`
then supplies every inverse-substitution branch. This is sufficient, with no
claim of optimality. Empty words and `M=0` have no generator branches.

## Polynomial/partition carrier

The polynomial carrier is A08's `OscPoly M`. Ordinary degree counts factors,
while the energy domain is the weighted sum `Σ (i.val+1) r(ν,i)`; these are
distinct bounds. The mode weight is `i.val+1` and the monomial Gram norm `∏ (m^k k!)`. The finite carrier is A05's actual
`FockSpace σ h` in fixed charges `Ns`; the map sends a polynomial monomial to
the corresponding ordered positive-current word on `groundKet h Ns`. The
two orientations must map injectively to distinct species; if they collide,
parts merge and the factorial Gram factor is wrong. Under injectivity, the
partition state with parts `m` has squared norm
`∏_m m^(count m) count(m)!`, exactly the A08 monomial norm. This is an
unnormalized map; no square roots occur.

Under `2K+|Nν|≤h` for each species, the Haldane Gram theorem gives an isometric
embedding on the weighted-energy-`K` polynomial domain. Its range is the span of
partition states with parts at most `M`; it is not the whole budget if `M<K`,
because required parts above the cutoff are absent. Selected word moments need
only the embedding and vacuum compatibility, not surjectivity. For `M=0`, the
oscillator carrier has only constants and the map has range the sea line.
The Gram and path-action contracts also require `0<h`, matching the positive
regulator premises of the Core Haldane Gram and current-margin APIs. The
degenerate `h=0` constants/empty-word cases are intentionally outside these
contracts rather than being silently folded into the same proof route.

## Word and moment theorem dependency

First prove the raw-current substitution on generators and words. Then prove
the monomial-to-partition map, weighted Gram identity, and vacuum pairing.
Creation compatibility follows by the definition of positive-current word
states. Annihilation compatibility follows by CH11's written-order lowering
formula, with the path-local margin above for every surviving partition
branch. Induction from the right edge of each word gives path intertwining and
then equality of vacuum matrix elements with `omega0`. Applying A08's inverse
Bogoliubov free-algebra homomorphism gives `omegaP`; the hypotheses are checked
on every expanded branch, not merely on the unsusbstituted word. Finite linear
combinations follow by linearity.

Nonzero squeeze examples must use the transformed observable. Raw finite-sea
currents in the unsqueezed sea have zero one-current expectation and the usual
vacuum contractions; they do not in general give the nonzero anomalous
quadratic contraction of `omegaP`. Word length remains explicit in every
regulator condition; no fixed lattice reproduces arbitrary degree.

## Core source anchors inspected

`A08OscillatorStates.lean` (oscillator generator and functional),
`Ch09DensityModes.lean` (actual partial-shift current),
`Ch10Heisenberg.lean` (`rho_signed_ccr`, margin
`|m|+|n|+K+|N|≤h`), `Ch11HaldaneCompleteness.lean`
(`lowering_through_word`, `partition_gram`, R2 and budget completeness),
`A04CurrentMargins.lean` (edge support and actual restricted actions), and
`A05MultiSpecies.lean` (joint carrier, species currents, joint Gram and basis).

These are audited source facts and a derivation, not evidence that the new S4
contracts have been proved. Any candidate Lean interface must encode the
branch coverage explicitly and may not assume intertwining or moment equality
as an admissibility field.

## Verified proof route (Phase B, 2026-10-19)

The source now proves all original contracts and the numerical wrapper. The
actual action proof uses a scalar-monomial invariant through the reversed
execution list. Its global R2 hypothesis controls live Haldane lowering.
When a lowering mode exceeds K, the selected species has energy below that
mode and the one-species negative-budget theorem applies. The explicit local
annihilation margin remains part of the reviewed certificate, although this
R2-based proof does not need to consume it separately. Neither that redundancy
nor the Gram cutoff is hidden as an optimal domain claim.

Vacuum-polynomial compatibility needs no upper energy bound: every nonconstant
monomial has positive energy in at least one active species and is orthogonal
to that species sea. The Gram theorem itself remains restricted to the
weighted-energy domain with R2. Its formal consequences include the restricted
zero-kernel theorem and cutoff-range/budget inclusions; no whole-budget
surjectivity or global finite CCR is claimed.
