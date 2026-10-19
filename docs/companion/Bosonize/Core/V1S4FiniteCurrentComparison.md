# V1-S4 exact finite current-word comparison

## Current phase — Phase C complete, 2026-10-19

Accepted source: `Bosonize/Core/V1S4FiniteCurrentComparison.lean`, SHA-256
`3f436b970c78bb5126a18ab0ffc4a523bea61dd855f60b491baf410f96770b3e`.
All eight original contracts and all added support/corollary proofs are complete.
The module contains 53 named lemmas/theorems and 92 named declarations in total.
Fresh complete audits through `import Bosonize` use only permitted standard
axioms; there are zero source placeholders and zero compiler warnings.

The independent mathematical/proof review and pedagogical review are PASS.
The promotion is byte-identical, preserves all 38 earlier Core sources and
records (39 now frozen), and migrates only the S4 statement-lock path. Both
strict guards and sandboxed local CI pass after promotion. S5 is untouched.
See `docs/plans/v1-s4/phase-c-acceptance-2026-10-19.md`, the complete review
record `docs/plans/v1-s4/independent-review-2026-10-19.md`, and the Phase C
build/axiom/CI/preservation receipts in that directory.

## Accepted declaration map

| Mathematical content | Declaration anchors |
| --- | --- |
| Actual finite-current free-word substitution | `theta`, `weight` |
| Numerical suffix certificate and full substitution branches | `BranchPath`, `PathCovered`, `inverseBranches`, `survivingBranches` |
| Exact inverse-Bogoliubov expansion | `inverse_expansion_contract`, `inverse_branches_length` |
| Unnormalized polynomial/partition map and weighted domain | `polynomialState`, `monomialState`, `weightedEnergy`, `PolynomialDomain` |
| Gram normalization and restricted zero kernel | `oscillator_monomial_norm_eq_haldane_contract`, `polynomial_state_gram_contract`, `polynomial_state_kernel` |
| Exact physical budget and cutoff-span inclusions | `polynomial_state_budget_contract`, `polynomial_state_range_contract` |
| Current insertion/lowering and rightmost-first induction | `Support.mono_creation`, `Support.mono_lowering`, `Support.execution_action` |
| Vacuum compatibility | `Support.vacuum_polynomial`, `constant_expectation` |
| Selected ordinary/dressed moments | `covered_word_action_contract`, `covered_word_moment_contract`, `covered_dressed_moment_contract` |
| Derived word-length wrapper and finite combinations | `uniform_margin_path`, `uniform_word_moment`, `uniform_dressed_moment`, `covered_word_sum_moment`, `covered_dressed_sum_moment` |

Pedagogical mapping: the new S4 section of `notes/md/ch20_CDW.md` explains
these constructions after its existing S2/S3 realizations. Its prior 321 lines
are preserved byte-for-byte; the independently reviewed 5,094-byte addition
covers dictionary, carriers, normalization, path/R2 hypotheses, proof argument,
expansion, examples and scope. The note links to this companion and Core source.
The code realizes selected free-sea observables, not an interacting finite
state or a physical field/vertex identity; cutoff range inclusion is not full
budget surjectivity. Combined path/R2 hypotheses are sufficient, not asserted
optimal. No push or release was performed.

The remaining sections retain historical Phase A/B provenance. Their candidate,
placeholder and pending-review statements describe those earlier snapshots;
they are superseded by this accepted status and the final receipts.

## Historical Phase A candidate interface

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

## Historical pre-lock review snapshot

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

## Phase B — action and moment proofs

All original S4 theorem placeholders have been replaced. The reviewed action
helper artifact is `.scratch/v1-s4-resume/Action.lean`, SHA-256
`766c977207fa0b754958a05874f87d811e072be6e2bcb6243bd4c38a871279ae`.
Reviewer `/root/s4_diagnosis` approved every helper and its action theorem
specialization. The execution induction tracks a scalar monomial and its
species energies, preserving the displayed product order through reversal.
Live lowering uses the R2-controlled partition action; out-of-budget modes
use a one-species negative-energy argument. No path premise assumes transport.

The reviewed vacuum/moment artifact is `.scratch/v1-s4-resume/Moment.lean`,
SHA-256 `f62713f89a2bb790190c9586835a8126e9ecd6d9cb42f1b458946501b3badcf4`.
The same reviewer approved both vacuum helpers and the two moment proofs.
Vacuum compatibility holds for all polynomials by positive-energy
orthogonality and finite linearity. In the dressed proof, every nonzero
inverse-expansion coefficient uses its own branch path hypothesis.

The integrated canonical module builds in the required namespace sandbox with
zero warnings and zero placeholders. The existing audit source reports only
standard axioms for all original contracts. Strict locks pass with 1259
headers and 1309 commands. Full helper/data axiom auditing and final review
are still required before promotion; these scoped reviews are not acceptance.

## Phase B complete — final independent review

Reviewer `/root/s4_diagnosis` issued PASS for the integrated mathematics and
proofs at source SHA-256
`3f436b970c78bb5126a18ab0ffc4a523bea61dd855f60b491baf410f96770b3e`.
The reviewed statement lock is
`bbca6e8c87a8afb69640485e1e408b4156bfa38dc5da7967fa221e9757c8c6e1`;
the full audit source is
`70d5ee20831851587694f971dbe8fb5ec715f07eeeba76abd899d6127d9e0a0b`
and its output is
`b5617c59ed2267a35286a63da0953c7a4ff27acc9183376d86e99fab005f376f`.
The reviewer independently ran strict locks, checked all 92 audit entries
against commands and permitted axioms, and inspected the absence of source
placeholders and prior-Core diffs. Compiler/axiom generation was executed by
the supervising agent in the required sandbox, not independently repeated by
the reviewer. There were no blocking findings.

The final additive numerical/linear/constant corollaries were separately
approved at scratch hash
`c0aabdaf41fe27fa34d2f48075b74caa77d41008f59e2a45603256659281d662`.
The numerical path proof uses remaining-length energy allowance; all inverse
branches preserve length. Kernel, constant/M=0, mixed-species and squeezed
fourth-order examples are included in the integrated final review.

All 53 named theorem/lemma declarations and all 92 named declarations in
total have complete permitted-standard-axiom audits. Zero source placeholders
and zero target compiler warnings. Full sandboxed `make ci` passes, including
both libraries and guard/verifier tests. The only `sorryAx` displayed in the
CI log belongs to the intentional negative test `Fixture.value`; it is absent
from the S4 axiom output. Strict locks pass (1268 headers / 1312 commands).
The reviewer approves byte-identical Core promotion, sole S4 path migration,
Core aggregator addition and complete-source freeze. Pedagogical review and
fresh post-promotion integration remain the Phase C gates.
