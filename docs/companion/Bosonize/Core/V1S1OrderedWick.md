# V1-S1 — Ordered Wick theorem and oscillator moments

Status: **Phase C complete.** Phase A independently reviewed and locked; all
proofs, Core promotion/freeze, axiom audit, local CI and independent pedagogical
review pass. Scope ends at S1.

## Carrier and conventions

The carrier is the existing uncompressed free complex oscillator algebra
`OscAlgebra M`, with finite modes `(orientation, i : Fin M)` and positive weight
`i.val + 1`. CCR hold in its polynomial representation and descend inside the
functional in arbitrary contexts. No literal free-algebra CCR is assumed.
The functional remains A08's `omegaP = omega0 ∘ bogoliubovMap(c,-s)`.

The 18 complete data declarations are `OscLinearForm`, `linearElement`,
`formOfGenerator`, `wordElement`, `contraction`, `wordForms`, `Pairing`,
`IsPairing`, `pairingWeight`, `orderedPairingSum`, `dressedLinearElement`,
`dressedGeneratorForm`, `dressedForm`, `deleteFin`,
`generatorContractionExpected`, `freePair`, `squeezedPair`, and
`squeezedTestForm`. Forms have no constant coordinate. Contractions are
complex bilinear, with no coefficient conjugation: `Q(f,g)=omegaP(Y_f*Y_g)`.
The generator table uses `AC=m*c²`, `CA=m*s²` for matching modes, and
`AA=CC=-m*c*s` for matching mode numbers and opposite orientations.
All other entries vanish. `HyperbolicPair` supplies only `c²-s²=1`; both
allowed signs are covered.

## Proven interface

All 25 theorem declarations are proved:

- `pairing_representation_ext` — canonical edge-set extensionality.
- `linearElement_zero`, `linearElement_add`, `zero_mode_form_eq_zero`,
  `linearElement_zero_mode` — evaluation and the empty mode carrier.
- `contraction_bilinear_left`, `contraction_bilinear_right`,
  `contraction_zero_left`, `contraction_zero_right`, `generator_contraction`,
  `contraction_coeff_formula` — the ordered table and arbitrary coefficients.
- `bare_to_dressed_conversion`, `dressed_form_evaluation`,
  `bare_in_dressed_coordinates`, `dressed_conversion_preserves_free_expectation`
  — the exact linear substitution and inverse direction.
- `omegaP_empty_word`, `omegaP_pull_through`, `omegaP_ordered_wick`,
  `omegaP_odd_word_zero` — empty normalization, ordered recurrence, explicit
  perfect-pairing sum and odd vanishing.
- `omegaP_single_odd_moment`, `omegaP_single_even_moment` — for arbitrary form
  Y and q=omegaP(Y²), odd moments vanish and the even moment is
  `(2k)! / ((2^k)*k!) * q^k`, with explicit natural-to-complex casts.
- `free_vacuum_order_sensitive`, `squeezed_test_variance`,
  `squeezed_test_fourth_moment`, `mixed_bare_dressed_word` — nonvacuity checks.

There is no Hermiticity hypothesis on the algebraic moment result, and no
new reality or nonnegativity claim for q. Zero forms, zero q, zero squeeze,
M=0, and k=0 are covered by the parameterized statements and their exact
normalizations. The unit-weight free example gives omega0(ACAC)=1. The
nonzero-squeeze pair (5/3,4/3), on the sum of four unit-mode generators, gives
q=2/9 and fourth moment 4/27. The mixed bare/dressed example gives m*c.

## Proof and pairing correspondence

Pull-through first holds in omega0. Expand the first form over its finite
support. Creator-leading terms vanish by the left vacuum boundary. Commute an
annihilator across each later form using A08's contextual CCR descent, with
arbitrary prefixes and suffixes; its terminal right boundary is zero. Each
scalar contribution is precisely the ordered two-point contraction. Finite
linearity and `dressedForm c (-s)` then transport the free recurrence through
the actual pullback. Positivity is not used as a factorization argument.

A public pairing is a finite set of edges (i,j), i<j, with exactly one partner
per position. The additive helper module proves the finite-subset matching
bijection. A pairing on `insert x S`, with x smaller than every label in S,
is uniquely equivalent to its partner y in S and a residual pairing on
`S.erase y`. Edge erasure and insertion are inverse. `sumOn_first` reindexes
by this bijection and factors out the weight C(x,y).

The main theorem applies that identity to sorted, distinct original position
labels. Erasing the selected label preserves word order and keeps repeated
forms as separate positions. At the full position set, the helper's `Good`
predicate is proved equivalent to `IsPairing`; `sumOn_as_sum` identifies the
subtype sum with the public all-edge-set sum, where invalid pairings contribute
zero. This establishes enumeration of every perfect pairing exactly once,
beyond a renamed recurrence.

Odd words follow by strong induction using ordered deletion. For moments,
replicate a single form: all n+1 contractions coincide, so
`m_(n+2)=(n+1)q*m_n`. Factorial induction proves the explicit quotient.

## Reviews and scoped history

Independent reviewer: `/root/s1_interface_review` (separate native reviewer).
Phase A corrected the mixed value from m*c² to m*c, distinguished the symmetric
ACAC estimate 1/2 from assigning the forward contraction both ways (2), added
the finite coefficient formula, and clarified the factorial denominator.

- Reviewed initial interface source: `2d69dc34c5eb6586808b1b707f16cb2e6dd0d12b3ae8089a9ab1a91be077ba31`.
- Reviewed repaired packet: `276d38958eb3f8a50de3da2b9ce2adec884f883037f78a592c6ef79e1be1d959`.
- Reviewed recurrence proof batch: `13d91e0f6f669c8d55fb49520cb36e1c51f5b4a2641596f4dfbac3d0f4e51a2e` — PASS.
- Full proof and helper/import amendment: main `a98a25d2ff6ee1c1414bdba5c0091790579c61d9c079ce6c2c8f66818aa26d44`, helper `33fefe1fafbdde6c544925a641ac8cdec496ce571f3036558500a53ddb0ddeff` — PASS.

The helper was separated after repeated local-let elaboration timeouts, recorded
in `LOG_DISCOVERY_AND_PIVOTS.md`; the mathematical argument stayed unchanged.
All existing declaration hashes were preserved in the reviewed amendment;
only the helper and its import were added. The Phase A lock commit is
`763ee42`, recurrence/moment batch `a96f4cd`, full pairing/amendment `a55645a`.

The Phase C proof/migration review passed. The main's stale candidate comment
was removed, then its helper import changed from staging to Core. No namespace,
data or theorem statement changed. The helper moved byte-identically. Only
the two scoped interface records moved; main import/context hashes changed,
all unrelated interface records and the 34 previous Core hashes were retained.

## Fresh validation — 2026-10-17

Compiler: Lean 4.35.0-rc4, commit `c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`.

- Final main source SHA-256: `f26d52cb29008f7d39030157368b7b9131bf14a4db173e97ef404062220852a9`.
- Final helper SHA-256: `33fefe1fafbdde6c544925a641ac8cdec496ce571f3036558500a53ddb0ddeff`.
- Final interface manifest SHA-256: `e9e1682040cbbed0f8eb9ddd42a65b59f50afbd14b62b1dfbebcb6d6499712d6`.
- Final Core manifest SHA-256: `cbe522f531b1bb0b0ac6950527b01ca2bfff32976a833c4898b68584f7c280af`.
- `lake build Bosonize BosonizeStubs`: PASS (3423 jobs in the combined build).
- `make lock-check`: PASS, 1114 statements, 1126 frozen commands, 36 complete
  Core sources; all 34 pre-existing Core sources are preserved.
- `make ci`: PASS, 69 guard tests, both library builds, 18 verifier/audit tests,
  `CI OK`. The verifier suite's deliberate sorry fixture is not an S1 theorem.
- Zero proof placeholders and zero compiler warnings in both accepted sources.
- The [reproducible aggregator audit](../../../plans/v1-s1/axiom-audit.lean)
  checks all 57 new declarations and 14 relevant A08 dependencies. All 71 use
  only `propext`, `Classical.choice`, `Quot.sound`; see the
  [audit output](../../../plans/v1-s1/axiom-audit.txt).

## Pedagogical mapping and scope

The synchronized exposition is A08's “Ordered Wick theorem and moments: S1
oscillator extension”, plus Chapter 20's bounded S1-input subsection. Original
reference exposition remains, with only the completed-work status corrected.
The planned companion link now resolves to this migrated document.
The reference formal vertices, charge algebra, physical-field dictionary,
finite interacting state comparison and analytic limits remain separate.
S2 can reuse the ordered contraction, conversion, Wick and moment interfaces;
S1 constructs no formal-series or vertex framework and makes no t=1 claim.

Sources: [ordered Wick and moments](../../../../Bosonize/Core/V1S1OrderedWick.lean)
and [pairing combinatorics](../../../../Bosonize/Core/V1S1PairingCombinatorics.lean).


### Final independent acceptance receipt

Reviewer `/root/s1_interface_review` returned **PASS** for proof, actual Core
migration and pedagogical synchronization. The final source hashes above and
note hashes `b60f542826cf2e594aee1030115adaceac5bcb90ff495a2d87a0042cd6ee77e5`
(A08) and `9a153a82e63f39a489d815c3558b6ff72c7134606ee2fc8e7169370123a23f59`
(Chapter 20) were rechecked. Reviewed companion content hashes before this
receipt/status update were `53e72ed371a8292bfab084643bf5a5b0207e34d9b97c53c90df1f9d849f85a7a`
(main) and `87b579237750fee343e984ccf6a85983997f9d241e7b74662770a233685d835f`
(helper). The previously reported companion-link issue is resolved by the
actual companion migration, and the stale proof/status text was replaced.
All four documents' relative links resolve. This completes the local A–B–C
cycle; no push, external publication or GitHub CI is claimed. Stop before S2.
