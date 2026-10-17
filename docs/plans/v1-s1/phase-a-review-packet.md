# V1-S1 Phase A: ordered Wick theorem for `omegaP`

Date: 2026-10-17. Status: **review candidate; not reviewed, locked, or proved**.

## Review target and exact source identity

This packet requests an independent mathematical and Lean-interface review of
the concrete oscillator-only S1 candidate below against the current promoted
A08 source and its companion. The checkout baseline was
`728987b0e939fd11a0dbfd29a8ecdc6a4368ca17`; the current working tree also has
pre-existing unrelated edits. The candidate Lean source is
`BosonizeStubs/V1S1OrderedWick.lean`; its current SHA-256 is recorded in the
companion and must be recomputed by the reviewer together with the A08/Ch19
hashes before review. The first independent review returned REVISE; its
resolved findings are recorded below.
No S1 lock record has been created.

Relevant current declarations are `OscMode`, `OscGen`, `OscAlgebra`,
`creatorGen`, `annihilatorGen`, `omegaP`, `bogoliubovMap`,
`omegaP_ccr_descends`, `omegaP_ccr_descends_aa`,
`omegaP_ccr_descends_cc`, `omegaP_mul_dressed_annihilator`,
`omegaP_dressed_creator_mul`, `omegaP_comp_bogoliubovMap`, and
`omegaP_commutator` in `Bosonize/Core/A08OscillatorStates.lean`.

## Proposed carrier and complete data

For each `M : ℕ`, use the finite coefficient space
`OscLinearForm M := OscGen M →₀ ℂ`. This describes exactly the homogeneous
linear span of the free generators: there is no scalar/constant coordinate.
For `f : OscLinearForm M`, define its evaluation in `OscAlgebra M` by the
finite sum

`linearElement f := ∑ g in f.support, (f g) • FreeAlgebra.ι ℂ g`.

The universal ordered contraction is

`contraction hp f g := omegaP M hp (linearElement f * linearElement g)`.

It is complex-bilinear, not sesquilinear. Coefficients are used as given in
both arguments; there is no coefficient conjugation. For a word
`w : List (OscLinearForm M)`, `wordElement w` is the product of its evaluated
forms in list order, with the empty product equal to `1`.

The source defines `Pairing n := Finset (Fin n × Fin n)` and an `IsPairing`
predicate requiring `i<j` for every edge and a unique partner for every
position. The finite pairing sum ranges over all finite edge sets and assigns
zero to those that do not satisfy `IsPairing`. Since each matching is exactly
its set of canonically oriented edges, this representation counts each
matching once; `pairing_representation_ext` proves extensional uniqueness.
The weight multiplies `contraction (w i) (w j)` along each edge `i<j`.

## Proposed theorem interface

The declarations in `Bosonize.V1S1` are parametric in `M`, the existing
`HyperbolicPair hp`, and arbitrary finite linear forms. They include the
following complete data and theorem contracts:

1. `OscLinearForm`, `linearElement`, `wordElement`, `contraction`,
   `Pairing`, `IsPairing`, `pairingWeight`, and `orderedPairingSum`.
2. `generatorContractionExpected`, `generator_contraction`, and the explicit
   `contraction_coeff_formula` summing `f i * g j * Q(generator_i,
   generator_j)` over the two finite supports, plus
   `dressedGeneratorForm`, `dressedForm`, `dressedLinearElement`, and the
   bare/dressed conversion contracts.
3. `omegaP_empty_word` and `omegaP_pull_through`. The latter uses
   `Fin tail.length`; `deleteFin tail i := tail.take i.val ++
   tail.drop (i.val+1)`, which retains the order of all surviving factors.
   Its empty sum handles a one-factor word.
4. `omegaP_ordered_wick`, with right side `orderedPairingSum hp f`, and
   `omegaP_odd_word_zero`.
5. For a single form `Y`, put `q = contraction hp Y Y`. Then for all `k`,
   `omegaP(Y^(2*k+1)) = 0` and
   `omegaP(Y^(2*k)) = (((2*k).factorial : ℕ) : ℂ) /
   (((2^k) * k.factorial : ℕ) : ℂ) * q^k`. Thus the denominator is the cast
   of `2^k` multiplied by `k!`, not the factorial of that product. The empty
   power is `1`.
6. Nonvacuity/edge contracts: zero-mode and zero-form behavior, zero
   contractions, an unsqueezed ordered `A C A C` example, a nonzero-squeeze
   variance/fourth moment, and a mixed bare/dressed word.

The pairing definition must support the recurrence-to-explicit-formula
proof: in every nonempty perfect matching, position zero has exactly one
partner `j > 0`; removing `{0,j}` leaves one perfect matching on the
remaining ordered positions. Conversely each such partner and residual
matching reconstruct exactly one original pairing. The code's canonical
edge-set representation provides the uniqueness; the remaining decomposition
lemma is a Phase B obligation.

## Source reconciliation: contractions and dressing

Write `A_{ν,i}=annihilatorGen M ν i`, `C_{ν,i}=creatorGen M ν i`, and
`m_i=i.val+1`. The proposal derived from the actual pullback
`omegaP = omega0 ∘ bogoliubovMap(c,-s)` is:

| Ordered input | `omegaP` value |
|---|---:|
| `A_{ν,i} C_{μ,j}` | `δ(ν,i),(μ,j) * m_i * c²` |
| `C_{ν,i} A_{μ,j}` | `δ(ν,i),(μ,j) * m_i * s²` |
| `A_{ν,i} A_{μ,j}` | `-δ_{j i} * m_i * c*s` when `μ=opposite(ν)`; otherwise `0` |
| `C_{ν,i} C_{μ,j}` | `-δ_{j i} * m_i * c*s` when `μ=opposite(ν)`; otherwise `0` |

Here `c,s` are the real fields of `hp`, cast to `ℂ`. In the anomalous rows,
the mode indices must agree and the species are opposite; the weight is then
unambiguous. Same-species anomalous terms and all unlisted mixed
annihilator/creator orientations vanish. The reviewer must verify all rows
against the polynomial representation and the current pullback direction,
including both signs of `s` and `c`.

Bare forms need no additional hypotheses. The conversion to dressed forms is
the inverse Bogoliubov substitution: `bogoliubovMap M c s` sends the bare
generators to dressed linear combinations and `omegaP ∘ bogoliubovMap(c,s) =
omega0` by `omegaP_comp_bogoliubovMap`. The coefficient map
`bogoliubovMap M c (-s)` expresses a bare linear form in the dressed
generators, using `bogoliubovMap_inverse_rev` and `hp.hyperbolic_id`. Review
must check the Bool/species flips explicitly; do not assume `CCR` as literal
equalities in `OscAlgebra`.

## Proof dependency order and review questions

1. Establish the `Finsupp` finite-sum representation, linearity, and
   `M=0`/zero-form behavior.
2. Establish the generator table from the exact pullback and polynomial
   vacuum, with no guessed textbook convention.
3. Extend the table bilinearly to `contraction` and establish the two vacuum
   boundaries for evaluated linear forms.
4. Prove annihilator pull-through by moving each annihilator through the
   finite ordered word. Use the contextual A08 descent lemmas at each prefix
   and suffix; use the terminal annihilator boundary to kill the remainder.
5. Convert bare linear forms, or equivalently apply linearity to dressed
   pieces, to obtain the declared arbitrary-form recurrence.
6. Prove the perfect-matching decomposition and explicit ordered pairing
   theorem by induction; derive odd vanishing and single-form moments.

The reviewer should specifically challenge: the recurrence's shortened-word
order; all CCR signs/species conditions; coefficient conjugation; the empty
and zero-mode cases; existence and uniqueness in the pairing enumeration;
factorial scalar types; zero squeeze and both hyperbolic parameter signs; and
whether any optional finite particle-hole, A10, field-dictionary, charge or
formal-series choice has accidentally entered the S1 hypotheses. None of
those optional scope choices is a premise here.

## Examples for nonvacuity and falsification

At `M=1`, weight one, free parameters `c=1,s=0`, the ordered table gives
`omega0(A C A C)=1`, since `Q(A,C)=1` and `Q(C,A)=0`. A symmetric-average
contraction `Qsym(X,Y)=(Q(X,Y)+Q(Y,X))/2` gives `1/2` for each orientation
and the pairing expression `1/2`, also incorrect. A different unordered
convention that assigns the forward `AC` value `1` to either orientation
gives `2`, also incorrect. These are distinct examples of why the ordered
contraction cannot be symmetrized. The theorem's required checked example is
the actual ordered expectation `1`.

For a nonzero squeeze, choose `c=5/3`, `s=4/3`, so `c²-s²=1`, and
`Y=A_R+C_R+A_L+C_L` at unit mode weight. The derived table gives
`q=omegaP(Y²)=2/9` and hence `omegaP(Y⁴)=4/27`. This checks the anomalous
cross-branch sign and fourth-moment normalization. Both examples are checks,
not substitutes for the parameterized theorem.

## Phase A validation and gate status

Baseline observed before S1 work: branch `main`, HEAD
`728987b0e939fd11a0dbfd29a8ecdc6a4368ca17`, toolchain
`leanprover/lean4:v4.35.0-rc4`; the checkout contains pre-existing unrelated
modifications and untracked planning files, all preserved. The exact A08 and
Ch19 source hashes are recorded in the companion. The staging target
`lake build BosonizeStubs.V1S1OrderedWick` passes with the expected theorem
placeholder warnings. The fresh data-only axiom audit passes for all 18 data
declarations with only `propext`, `Classical.choice`, and `Quot.sound`.
Existing baseline strict stub and Core locks pass (1079 statements/1093
commands; 34 Core files). The candidate itself is not locked yet.

**Gate:** the exact Lean interface and its mathematical meaning have passed
independent review. Lock only this reviewed source and proceed with its Phase B
proofs. Do not include any other unreviewed staging entry in the lock update.

## First independent review and resolutions

Reviewer `/root/s1_interface_review` returned **REVISE** for the first
candidate. The review confirmed the A08 signs, species conditions, bilinear
coefficient convention, inverse dressing direction, pairing representation,
moment coefficient, and stated boundary cases. It identified a false mixed
bare/dressed example: for `A_R` followed by dressed `C_R`, the expectation is
`m_i*c`, not `m_i*c^2`. The candidate statement has been corrected to the
source-derived value `((i.val+1 : ℕ) : ℂ) * (squeezedPair.c : ℂ)`.
The reviewer also distinguished the symmetric-average incorrect pairing value
`1/2` from the forward-value-for-either-order incorrect value `2`. Finally,
`contraction_coeff_formula` now states the finite-support bilinear table
explicitly. These changes require re-review of the updated source and
companion hashes before lock creation.

## Final Phase A independent review receipt

Reviewer: `/root/s1_interface_review` (independent native review agent).
Final verdict: **PASS** after resolving the findings above. The reviewer
checked the exact interface, source-grounded contractions, coefficient
convention, dressing direction, recurrence order, canonical pairings and
decomposition feasibility, moments, edge cases, examples, and oscillator-only
scope. The final review also resolved the packet's factorial grouping.

Reviewed identities:

- Lean candidate:
  `2d69dc34c5eb6586808b1b707f16cb2e6dd0d12b3ae8089a9ab1a91be077ba31`.
- Normative review packet (after the factorial correction):
  `276d38958eb3f8a50de3da2b9ce2adec884f883037f78a592c6ef79e1be1d959`.
- Companion at review time:
  `e6928385df054c490b8d24ce3522783c8888253cfaf9ab542e10dd0051a89a37`.
- A08 dependency:
  `ed3ef9f87c9be26460004fd52efbdd7f0a2490b544c990cc89e6178f0a97ee35`.
- Ch19 dependency:
  `845e95b619fca515b25c2a103071ba1fa0fdfa46ddd12081440ddfbdae902339`.

Fresh candidate validation on the reviewed Lean hash: `lake build
BosonizeStubs.V1S1OrderedWick` succeeded with 24 expected Phase A sorry
warnings. `python3 scripts/webllm/audit_axioms.py --data-only
BosonizeStubs/V1S1OrderedWick.lean` passed all 18 data declarations using only
`propext`, `Classical.choice`, and `Quot.sound`. This is elaboration and data
axiom evidence only; the theorem contracts remain unproved. The reviewed
interface is now added to `docs/spec/stub_locks.v2.json`; the updated lock SHA-256
is `1206443e2ec861be2f3c413f4e03bc63ee55686ed1a2ca96c060f6c41bd0a808`.
