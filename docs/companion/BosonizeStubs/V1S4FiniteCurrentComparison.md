# V1-S4 exact finite current-word comparison

## Current phase

**Phase B in progress, resumed 2026-10-19.** The reviewed Phase A interface
was locked in `7f623b1`, with the positive-regulator amendment in `2e2be41`.
Three contracts remain unproved: covered word action, covered word moment,
and dressed moment. No S4 promotion or Phase C claim.
Historical review snapshots below describe their recorded dates, not current
placeholder counts.

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

## Phase B resume — 2026-10-19, first proof batch

The inverse-Bogoliubov expansion is now proved by word induction. Its two
head images are disjoint because the creation bit flips, so the finite-set
sum splits without lost multiplicities; coefficients multiply in displayed
order. The monomial norm equality is proved by counting repeated positive
mode labels and extending the Hall product over all cutoff modes.

Independent reviewer `/root/s4_diagnosis` approved removing the unused
`σ`, instance, species-map and injectivity binders **only** from
`oscillator_monomial_norm_eq_haldane_contract`: neither side depends on them.
The equality itself is unchanged. The Gram/action hypotheses retain species
injectivity. Reviewed pre-amendment source hash:
`af1976a648af9b4f4c5388aa2fc2ede99ada3fbccb052d9ae83aca1e0583c4d7`;
reviewed scratch norm proof hash:
`0da7b86f02f227b1c2c0125a2ca3be9fd73c36ddc4cc146facbed3298f8c7189`.
Verdict: approve this exact binder removal; not sprint/proof acceptance.

Fresh sandboxed module build passes with exactly four remaining `sorry`
warnings and no other S4 warnings. The audit in
`docs/plans/v1-s4/phase-a-audit.lean` confirms standard axioms only for the two
new proofs and existing range/budget proofs. The four unfinished contracts
still depend on `sorryAx`. Strict lock verification passes; manifest records
outside this S4 staging file are unchanged.

The independent read-only action diagnosis found the path condition adequate.
Use a scalar-monomial invariant along `w.reverse`, canonical-list count,
creation/erasure lemmas, and `A05.word_tensor`/`rho_tensor`. Live lowering uses
`Ch11.lowering_through_word_erase`; a killed species branch uses the
one-species `Ch09.rho_lowering_budget_zero`, since another species can carry
energy. This diagnosis is not a proof or acceptance verdict.

## Phase B — polynomial Gram batch

Reviewer `/root/s4_diagnosis` approved the additive `Support` bookkeeping
helpers and the Gram proof, preserving all existing data and theorem headers.
Reviewed helper artifact SHA-256:
`0dd894faa7b6b62338c3109dccf629c6a2c1cdeda214382ee4a86274299972fc`.
The review covers positive mode counts, energies, insertion/erasure of one
part, exponent recovery, species separation and product normalization. The
reviewed source before integration was
`2a677303f9a61f68e1befc4eebc8c2648f032fa4072a703fbedc8b9567579f7e`.
Verdict: approve the specified helper amendment and Gram proof integration;
not final acceptance.

The canonical module now proves `polynomial_state_gram_contract` by tensor
factorization, the actual one-species `word_gram` theorem and finite support
sums. The sandboxed module build passes with only three remaining `sorry`
warnings. A fresh axiom audit of this contract contains only the permitted
standard axioms. Strict locks pass after adding only the reviewed S4 helper
records (1242 theorem headers / 1302 commands globally). No existing Core or
other staging records changed. The scoped manifest diff against the initial
baseline is kept free of unrelated ordering/serialization changes.
