# V1-S4 exact finite current-word comparison

## Current phase

Phase A candidate after two independent review rounds. The latest verdict is
REVISE; no scoped lock exists, no Phase B proof work has begun, and no Phase C
pedagogy has been changed. The accepted outcome remains pending.

## Candidate interface

Source: `BosonizeStubs/V1S4FiniteCurrentComparison.lean`.

The candidate defines the actual A05 free-sea current substitution, species
resolved rightmost-first path certificates, coefficient-filtered inverse
Bogoliubov branches, weighted polynomial energy, monomial/current states, and
a formal cutoff-range subspace. It includes the uniform sufficient margin
`2*d*M + |Nν| ≤ h` as a corollary of local annihilation margin arithmetic.

There are eight theorem placeholders in unaccepted Phase A staging: inverse
expansion, monomial norm, polynomial Gram, polynomial budget, polynomial
range, covered word action, unsqueezed moment, and dressed moment. These are
contracts only and establish no S4 result. The example declarations instantiate
the moment contracts with explicit path hypotheses; their conclusions still
depend on those placeholders.

## Exact current review snapshot

* Lean source: `804f72a4ce81b0173675357376a57c86bbb06a5d0496de3968fc2f5d55e4baf0`
* Derivation: `493d13ef9dd6ae06c5e568bde37e3571396f3a06ae8a36927c78eebce208cf17`
* Phase A axiom audit source: `531ef7e4e66ad12135328e3ea4e0a9c434ab0f7b64ada1c5d9ce1633e42d854d`

Candidate module build succeeds under `leanprover/lean4:v4.35.0-rc4`. Its
only warnings are the eight intentional theorem placeholders; no other
candidate linter warnings remain. The data audit succeeds: data definitions
and arithmetic lemmas use only `[propext, Classical.choice, Quot.sound]`; all
eight theorem contracts depend on `sorryAx`, as expected in Phase A.

## Independent review history

Reviewer: `/root/v1s4_review` (independent native diagnosis agent; no file edits).

### Round 1 — REVISE

Reviewed hashes:

* Lean: `14c5a5713eb3c588045a9976718a364559c75ea9a88bac97e02d8e84124a218e`
* Derivation: `d7149f37995def6cb9f9ce07ad2d17256de87e90a767608a21c26d30968d5008`

Findings: energies must be per species; injective species mapping is needed
for Gram normalization; positivity/path conditions cannot be replaced by a
coarse margin; inverse branches require coefficient-aware coverage; polynomial
energy/domain/range must be precise; examples were insufficient. The revised
candidate addressed the first four and described the range cutoff.

### Round 2 — REVISE

Reviewed hashes:

* Lean: `a5eb55886dd5be66fdbc4de03685b4a4ff75999f1be14bb87a306636a2ed9dde`
* Derivation: `766111ac06140055c07284010cd9640d3132b1cbe381c3703fd5d540a3004ad2`
* Audit source: `531ef7e4e66ad12135328e3ea4e0a9c434ab0f7b64ada1c5d9ce1633e42d854d`

Findings: (1) polynomial factor degree was used as energy; replace with
weighted energy; (2) a killed annihilator still needs the finite-current
source margin or an independent support proof; (3) examples must instantiate
moment comparison contracts, including nonzero squeeze and fourth order; and
(4) formalize the range inclusion. These are resolved in the current candidate
by `weightedEnergy`, requiring the exact margin before either live or killed
annihilation, explicit unsqueezed/dressed/fourth-order theorem applications,
and `polynomial_state_range_contract`. This resolution record is awaiting
independent reassessment of the exact hashes above.

## Mathematical dictionary and margins

A08 `true` (multiplication/creation) maps to `A05.rho h ν +(i.val+1)`;
A08 `false` (weighted derivative/annihilation) maps to
`A05.rho h ν -(i.val+1)`. This follows CH09's nonwrapping `dGamma` shift and
A05's species lift. There is no square root or sign reversal. The map extends
by the free algebra and does not assert global finite CCR.

For each species, a live annihilator at energy `Eν` needs
`m + Eν + |Nν| ≤ h`, the CH10 margin after writing `Eν=n+Rν` for each
remaining positive-current partition factor. A branch certified as killed
still requires this source margin to invoke the actual finite-current action
identity before using its zero result. Energies and positivity are tracked per
species; displayed products act rightmost first. Only nonzero-coefficient
inverse branches require path coverage. The uniform bound
`2*d*M + |Nν| ≤ h` bounds a live prefix and the Haldane R2 domain but does not
replace the explicit path certificate.

## Polynomial map and range

`weightedEnergy r = Σ_(ν,i) (i.val+1) r(ν,i)` is distinct from ordinary
factor degree. `PolynomialDomain K` uses weighted energy. The unnormalized
monomial map uses ordered positive-current partition states; under injective
orientation-to-species assignment its Gram factors equal A08's
`∏ m^k k!`, without square roots. The formal range contract places the image
in the span of cutoff modes. When `M<K`, the map need not span the full budget;
selected word moments do not require surjectivity.

## Scope

Only transformed observables in an actual free finite sea are intended. This
does not establish an interacting state, physical field/vertex equality,
global finite CCR, automatic removal of intermediate projection residuals,
finite particle-hole symmetry, analytic/continuum claims, or S5. Stop after
S4; S5 has not started.

### Round 3 — PASS for Phase A interface

Reviewer `/root/v1s4_review` confirmed these exact final pre-lock hashes:

* Lean: `804f72a4ce81b0173675357376a57c86bbb06a5d0496de3968fc2f5d55e4baf0`
* Derivation: `493d13ef9dd6ae06c5e568bde37e3571396f3a06ae8a36927c78eebce208cf17`
* Audit source: `168ce7e9c0a02ab6f83122026903432762f3a2e16ee43c15f0e67279678b7633`

Verdict: PASS. The reviewer explicitly limits this verdict to Phase A interface
review; the eight theorem placeholders still require Phase B proofs. The
post-review wording-only edits were hash-confirmed by the same reviewer.

### Scoped amendment — positive-regulator proof premises

After Phase B API diagnosis, reviewer `/root/v1s4_review` approved the narrow
proposal to add `0 < h` to `polynomial_state_gram_contract` and
`covered_word_action_contract`. The available Core Gram and current-margin APIs
require this premise. The alternative would retain `h=0` by splitting the
constant/empty-word cases; the positive-regulator premise is the minimal direct
match to the selected proof route. No other contract changes are authorized.
The derivation now records this boundary. The amended source and lock manifest
are awaiting exact-hash Phase A re-review; the earlier PASS does not cover the
amended signatures.
