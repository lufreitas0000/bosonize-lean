# V1-S1 ordered Wick theorem — Phase A companion

Status: **Phase A interface independently reviewed and passed; reviewed lock
is the next gate. The theorem contracts remain unproved.**

The proposed result is an algebraic theorem on the existing uncompressed
`OscAlgebra M = FreeAlgebra ℂ (OscGen M)` carrier, evaluated by the existing
Bogoliubov-pulled-back functional `omegaP M hp`. It does not identify the
functional with a finite CAR state or a finite-dimensional CCR
representation.

The candidate finite-dimensional space of homogeneous linear forms is
`OscLinearForm M := OscGen M →₀ ℂ`; `linearElement` evaluates by the finite
sum of each coefficient times its free generator, with no constant
coordinate. `contraction hp f g` is
`omegaP M hp (linearElement f * linearElement g)`, complex-bilinear in the
coefficients, with no conjugation. `wordElement` preserves list order and
uses `1` for the empty word. `dressedGeneratorForm`, `dressedForm`, and
`dressedLinearElement` give the finite linear change of variables induced by
the actual A08 `bogoliubovMap`.

`Pairing n` is the finite set type `Finset (Fin n × Fin n)`;
`IsPairing P` requires each edge `(i,j)` to satisfy `i<j` and every position
to have exactly one partner. `orderedPairingSum` sums over every finite edge
set and contributes zero for non-pairings. A matching has a unique canonical
edge set, and `pairing_representation_ext` establishes extensional
uniqueness. The partner-of-position-zero decomposition needed to connect the
recurrence and explicit sum remains a theorem obligation.

The module declares 18 complete data items and 25 theorem declarations.
Phase A independently reviewed and locked all 25 statements. During Phase B,
24 theorem declarations now have complete kernel-checked proof bodies, including
pull-through, odd-word vanishing, both single-form moment formulas, and the
nonzero-squeeze fourth moment. The sole remaining placeholder is
`omegaP_ordered_wick`, the explicit sum over perfect pairings. The first-partner
pairing decomposition remains the outstanding combinatorial obligation.
See the exact Lean signatures in
[`V1S1OrderedWick.lean`](../../BosonizeStubs/V1S1OrderedWick.lean)
and the natural-language review packet at
[`phase-a-review-packet.md`](../plans/v1-s1/phase-a-review-packet.md).

The expected dependency chain is:

1. exact generator contractions from the current `omegaP` pullback;
2. bilinear extension and bare-to-dressed conversion;
3. pull-through from the A08 vacuum boundary identities and contextual CCR
   descent;
4. a perfect matching representation whose partner-of-first-position
   decomposition is a bijection;
5. ordered pairings, odd vanishing, and the single-form factorial moments.

The generator table, theorem contract, proof plan, required examples, source
anchors, and unresolved review questions are mirrored in
[`phase-a-review-packet.md`](../plans/v1-s1/phase-a-review-packet.md). That
packet is normative for the proposed Phase A review. Its table is derived
from the actual A08 definitions but remains subject to independent
verification.

The theorem depends only on the finite oscillator mode set and the existing
`HyperbolicPair` hypothesis. It includes `M=0`, zero forms, zero squeeze, both
allowed signs of `c,s`, and mixed bare/dressed forms by linear conversion.
Hermiticity is not required for the algebraic moment formula. Positivity can
be used separately to show a Hermitian variance is real and nonnegative;
that is not part of Gaussian factorization.

S1 stops before charge/Klein vertices, formal series, physical field
identification, finite particle-hole maps, A10, finite-QMB integration,
analytic convergence, or continuum/thermodynamic claims. S2 may reuse only
the accepted ordered contraction and moment interface once its own Phase A
review begins.

Independent interface reviewer `/root/s1_interface_review` returned **PASS**
after two review rounds. The first returned **REVISE** and found that the
mixed bare/dressed check claimed
`m_i*c^2` where the A08 pullback gives `m_i*c`; the Lean contract now states
the corrected value. It also required distinguishing the symmetric-average
counterexample (`1/2`) from assigning the forward contraction both ways (`2`),
and requested the explicit coefficient-sum formula. All three findings are
resolved in the candidate. A second review found ambiguous factorial grouping
in the packet; it was corrected to cast `(2^k) * k.factorial` to `ℂ`, and the
reviewer returned PASS on that exact packet hash. The reviewed S1 interface is
now the sole new record in the v2 lock. Current Phase B changes are proof
bodies only; no statement or definition has changed.

## Source identities at candidate preparation

- `Bosonize/Core/A08OscillatorStates.lean` — SHA-256
  `ed3ef9f87c9be26460004fd52efbdd7f0a2490b544c990cc89e6178f0a97ee35`.
- `Bosonize/Core/Ch19Correlations.lean` — SHA-256
  `845e95b619fca515b25c2a103071ba1fa0fdfa46ddd12081440ddfbdae902339`.
- Reviewed Lean candidate — SHA-256
  `2d69dc34c5eb6586808b1b707f16cb2e6dd0d12b3ae8089a9ab1a91be077ba31`.
- Reviewed packet — SHA-256
  `276d38958eb3f8a50de3da2b9ce2adec884f883037f78a592c6ef79e1be1d959`.
- Companion at review time — SHA-256
  `e6928385df054c490b8d24ce3522783c8888253cfaf9ab542e10dd0051a89a37`.
- Updated scoped v2 lock — SHA-256
  `1206443e2ec861be2f3c413f4e03bc63ee55686ed1a2ca96c060f6c41bd0a808`.

## Phase B checkpoint (2026-10-17)

A second independent troubleshooting pass on the structural goals confirmed
the proof route and found no mathematical obstruction. It recommends proving
pull-through first for `omega0`, by commuting an annihilator generator across
each form with the contextual A08 CCR descent and vacuum boundaries, then
transporting the result through the Bogoliubov pullback. For explicit
pairings, decompose by the unique partner of position zero and transport the
residual edge set along `Fin.succAbove`; this gives an exact finite bijection
and matches the ordered deletion recurrence. The current edge-set pairing
representation needs no interface amendment.

The earlier quota pause was incorrect: `usedPercent = 4` meant 96% of the
weekly allowance remained. On resumption the tool reported 28% used in the
five-hour window and 4% used weekly. The usage guard permits continued S1 work.

The independently reviewed recurrence source SHA-256 is
`13d91e0f6f669c8d55fb49520cb36e1c51f5b4a2641596f4dfbac3d0f4e51a2e`.
Reviewer `/root/s1_interface_review` returned **PASS for pull-through** on this
exact source and unchanged A08 hash. The proof expands one free generator,
uses contextual CCR descent with arbitrary algebra prefixes and suffixes,
commutes it through the ordered tail, and applies the vacuum boundaries.
`dressedForm c (-s)` then transports this recurrence through the actual
`omegaP = omega0 ∘ bogoliubovMap(c,-s)` pullback. No literal free-algebra CCR
or double dressing is used.

A fresh audit of all 43 declared items reports only `propext`,
`Classical.choice`, and `Quot.sound`, except for `omegaP_ordered_wick`, which
still reports `sorryAx`. In particular pull-through, odd words, both factorial
moment theorems, and the squeezed fourth moment have no inherited placeholder.
The fourth moment is `3 * (2/9)^2 = 4/27`; no Hermiticity hypothesis is needed.
`lake build BosonizeStubs.V1S1OrderedWick` passes with one placeholder warning;
strict interface verification passes 1104 statements and 1115 frozen commands;
Core preservation verifies all 34 existing complete sources. The reviewer
explicitly does not approve Phase B or Phase C while the pairing theorem remains
unfinished. Continue the pairing-removal/reconstruction proof; do not start S2.

At Phase A, `lake build BosonizeStubs.V1S1OrderedWick` elaborated the S1 data and
single-sorry theorem contracts. It emits only the expected placeholder
warnings in the candidate, plus informational tactic suggestions from two
existing dependencies. Fresh data-only axiom audit passes all 18 data items
with only `propext`, `Classical.choice`, and `Quot.sound`. This establishes
Phase A elaboration and data axioms, not theorem correctness or proof.

## Baseline checks (2026-10-17)

- `python3 scripts/guards/stub_lock.py --check --strict`: baseline PASS,
  1079 statements and 1093 frozen commands. The new unreviewed candidate is
  intentionally not in the lock yet.
- `python3 scripts/guards/core_lock.py`: PASS, 34 complete Core sources.
- `lake build Bosonize BosonizeStubs`: PASS, 3421 jobs. Existing replayed
  dependencies emitted informational tactic-suggestion messages; no build
  failure occurred.
