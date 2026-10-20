# V1-S6 Phase A companion: physical fields and controlled residuals

Status: **Phase B in progress**. The current typed decomposition and
quantitative comparison have independent review. The CDW discarded-channel
norm bound is now proved; the h3 ground-image bound remains open. The reviewed interface is now scoped-locked.
No promotion has been created. Review receipts and exact hashes are in [the
entry-review receipt](../../plans/v1-s6/entry-review.md).

## Mathematical target and rejected stronger claims

The actual finite CAR field `A` and CH14's finite Taylor/Klein candidate `B`
are not asserted equal. The S6 dictionary target is a sharp full-ground-image
obstruction at `h=3`, `M=1`, `Kin=0`, `Kout=2`, periodic twist and `x=0`.
The corresponding exact image calculation is in the entry-review receipt.
It keeps the physical normalization, source-first zero-mode phase, Klein
charge shift, lowering `wPlus`, signed raising `wMinus`, Taylor order, and the
actual target projection. S2's coefficientwise Weyl-type series on its
charge-vector tensor polynomial carrier is a third object and is not identified
with either field.

The obstruction disproves a proposed unconditional or margins-only CH14
full-ground-image identity. It does not refute CH14's conditional theorem
`field_vertex_of_common_residual`, whose full-vector ground, cyclicity, and
common residual premises remain explicit. It establishes no global field
theorem, finite CCR, analytic evaluation, or state equivalence.

For actual products the accepted CH20 definitions remain authoritative:

```text
P_t A B P_s = P_t A P_m B P_s + P_t A (1-P_m) B P_s.
```

When the selected intermediate oscillator/partition carrier embeds by `U_m`
into an ambient finite budget, the map `U_m U_m†` is only its range projection.
The additional omitted-range term `P_m-U_m U_m†` remains in the transported
decomposition until its vanishing is proved. Endpoint carriers are represented
by isometric embeddings and their actual adjoints. Their selected domains are
therefore part of the theorem; no endpoint onto claim is used.

## Candidate data and theorem list

`IsometricEmbedding` stores a finite-dimensional continuous linear map and a
certified Hilbert adjoint. `adjoint_map` records `U†U=id`; there is no
surjectivity field. `OrthogonalProjection` stores an idempotent, self-adjoint
ambient projection. The theorem hypothesis `hUm` proves that the intermediate
embedded range lies inside that ambient budget. `rangeProjection`,
`intermediateResidual`, and `omittedRangeResidual` are computed from these
actual maps.

The candidate theorem list submitted for independent review is:

1. `typed_product_decomposition`: for `A : H_m → H_t`, `B : H_s → H_m`,
   endpoint embeddings `U_s,U_t`, and intermediate embedding `U_m`, decompose
   `U_t† A B U_s` into `(U_t† A U_m)(U_m† B U_s)`, the ambient projection
   residual `U_t† A (1-P_m) B U_s`, and omitted embedded-range residual
   `U_t† A (P_m-U_mU_m†) B U_s`.
2. `quantitative_product_comparison`: an operator-norm bound with the two
   residual norms and the independent finite-dictionary errors
   `||Ahat-VA|| ||Bhat|| + ||VA|| ||Bhat-VB||`. State and dispersion errors are
   intentionally not operator terms; they enter only a separate expectation or
   Hamiltonian comparison, neither of which the selected physical product
   theorem makes.
3. `h3_m1_ground_image_mismatch`: the norm of the exact finite-dictionary
   error on the specified source ground vector is at least `1/(2 sqrt(6))`.
4. `cdw_discarded_channel_norm_lower_bound`: strengthen CH20's existing
   nonzero witness to a `1/4` lower bound on the norm of the retained projected
   residual acting on the normalized source sea. The target-zero witness
   remains the adjacent exact-zero contrast.

The proof of `quantitative_product_comparison` now applies the exact typed
decomposition, expands the difference of the two finite candidate products as
`(Ahat - VA) Bhat + VA (Bhat - VB)`, and bounds each composition by operator
norm submultiplicativity. Its independent review passed on the exact source
hash in the receipt. The CDW lower bound is now proved as recorded below;
the h3 lower-bound contract remains unproved.

All exact declarations are in
[`V1S6PhysicalFields.lean`](../../../BosonizeStubs/V1S6PhysicalFields.lean).
The first independent pre-lock review returned REVISE on an earlier source
hash. Its projection finding was resolved by explicit
`OrthogonalProjection` data and the `hUm` range-inclusion hypothesis. Its
mode-error finding led to `finiteDictionaryError` and the strengthened h3
norm-lower-bound contract. The companion hash mismatch was a stale in-document
hash and was removed. Independent focused re-review then returned PASS on the
exact source, companion, receipt, and S0 hashes recorded in the receipt. This
is interface/coverage approval only, not proof approval.

## Carrier, phase, adjoint, and normalization conventions

- Ambient CAR maps use A05's finite Fock carrier. Each selected budget has its
  actual subtype inclusion. Source, middle, and target charge/budget indices
  are independent.
- `U_m` embeds a selected finite oscillator/partition carrier in the ambient
  middle budget. It is not treated as onto. The residual is typed from the
  original source carrier to the original target carrier.
- The adjoint convention is `⟨Uu,h⟩=⟨u,U†h⟩`, conjugate-linear in the first
  complex slot. Composition acts right to left.
- CH14 `wPlus` lowers and `wMinus` is signed raising; their adjoints carry the
  minus signs already in Core. The physical field retains the A01
  `L^(-1/2)` normalization and the external species twist. No scalar is chosen
  to force agreement.
- The candidate has the source phase before Klein lowering, then `wPlus`, the
  cutoff transition, and `wMinus`. The M=1 mismatch uses periodic twist and
  `x=0`, but the theorem statement fixes those values rather than generalizing
  their cancellation.
- CDW is the actual `c_R† c_L` product; SC is `c_R c_L`. Adjoint factor order
  is preserved. The S2 Weyl, bare-normal and dressed-normal conventions remain
  separate.

## Five-error ledger

| Obligation | Exact definition/carrier | Controlling result or S6 status | Coverage limit |
|---|---|---|---|
| Intermediate projection | `U_t† A (1-P_m) B U_s`, plus CH20's exact finite CAR residual on the source/target budgets | `typed_product_decomposition`; proved numerical lower bound `1/4` in `cdw_discarded_channel_norm_lower_bound` | Nonzero example does not characterize all charges or cutoffs. |
| Mode truncation and omitted range | Finite-mode dictionary errors are `Ahat-VA` and `Bhat-VB` on the selected finite carriers (`finiteDictionaryError`); the separate omitted range is `U_t† A (P_m-U_mU_m†) B U_s` | The quantitative theorem bounds the candidate errors multiplied by the companion factor norms. The pending h=3, M=1 contract states `||(Ahat-VA)ground|| ≥ 1/(2 sqrt(6))` by its extra orthogonal target component. The product decomposition retains the omitted-range map. | This lower bound is for the complete physical-to-CH14 candidate error on that vector; it does not attribute the discrepancy solely to missing modes. In the selected CH20 product witness no oscillator range is substituted, so no omitted-range approximation is made there. The general theorem has no blanket omitted-range bound. |
| Normal ordering and normalization | Physical CAR field vs fixed CH14 candidate vs S2 formal Weyl/bare/dressed definitions; keep scalar prefactors in their source definitions | The S0 equal-point free-sea computation reports physical `1/4` vs formal Weyl `1/16`, discrepancy `3/16`; this is distinct from the h=3 M=1 vector obstruction and from bare/dressed scalar factors. | No field rescaling and no global normalization theorem. The equal-point calculation must be separately established in the accepted proof package before it is promoted as a Lean result. |
| State comparison | Difference of expectations under a specified physical state and model state for a fixed observable dictionary | No state is substituted in either selected operator comparison, so this term is absent by construction; S5 state existence and S4 free-sea results are not an interacting-state estimate | This says nothing about a later physical-vs-model expectation comparison. |
| Dispersion/Hamiltonian | Finite operator difference for any chosen change of dispersion/Hamiltonian | No Hamiltonian or dispersion is changed in either selected finite operator comparison, so this term is absent by construction | The omission gives no spectral projection or ground-state stability theorem. |

No state or dispersion term appears in the selected operator norm inequality.
That absence is exact: it compares fixed operators on selected finite carriers,
with no state substitution and no Hamiltonian approximation. If a later
expectation comparison is formed, state error must be
defined on its actual observable dictionary. If a Hamiltonian is changed, the
dispersion term must be defined on that finite carrier and cannot be inferred
from the operator product theorem.

## Data audit and validation

The module uses only complete structure and function definitions. The ground
vector, charge sector, cutoff, twist, candidate, and residual are all actual
Core declarations. The Phase A draft had four permitted placeholders. Proof work has since begun;
the current source hash and proof status are recorded in the receipt.
The zero-charge admissibility proof is complete. The S6 target built with
`lake build BosonizeStubs.V1S6PhysicalFields` (3443 jobs). It now reports one
unproved concrete norm bound (h3) and no S6 linter warnings. This is a focused
build, not a full acceptance audit. The earlier Phase A data-only audit covered
six declarations; a fresh complete declaration and axiom audit is still
required after S6 proofs are finished.

The S6 entry is in `docs/spec/stub_locks.v2.json`; strict verification passes.
The full lock file was updated by adding only the S6 entry, preserving all
pre-existing entries byte-for-byte. Exact source and lock hashes are recorded
in the receipt. Any future interface change requires a reviewed scoped
amendment; proof-body changes remain subject to fresh proof review and audits.

Dependencies are accepted `Ch14Mandelstam`, `Ch20CDW`, and S5's finite model.
No new helper in frozen Core is proposed. If the independently reviewed
mathematics requires a changed carrier, theorem, or error metric, revise this
staging draft and re-review it before locking.

## CDW quantitative witness proof — 2026-10-20

`cdw_discarded_channel_norm_lower_bound` is complete and independently reviewed
at source SHA-256
`0f67cda15a756f77a82b2d19caff9b6d4557eee75a7c235c13091547cd809644`.
The proof reproduces the relevant local argument from
`Ch20.concrete_discarded_channel_nonzero` inside the existing theorem body;
no inaccessible private declaration is referenced and no Core source changes.

Write `S` for the actual source sea, `k=-1`, `p=+1`, and
`T=insert (0,p) (S.erase (1,k))`. The proof establishes that `T` is in the
charge `(1,-1)`, excitation-one target budget. The erased intermediate has
excitation at least one and is rejected by intermediate budget zero. Equality
with `T` determines the unique contributing pair `(k,p)=(-1,+1)`.
After the target projection the coefficient is exactly

```text
normalization(4) *
  (character(-1,1) * sign((1,-1),S) * star(normalization(4)) *
   star(character(+1,1)) * sign((0,+1),S.erase(1,-1))).
```

Each character and sign has norm one. The two normalizations each have norm
`1/2`, so the coefficient norm is exactly `1/4`. Cauchy–Schwarz with the
normalized ambient occupation ket bounds this coefficient norm by the output
norm. The target budget subtype has its inherited ambient norm; the final
`exact hbound` checks the definitional passage through the actual inclusion.
All auxiliary statements are local to this proof body.

Reviewer `/root/s6_cdw_review` returned **PASS** on the exact source hash above
and independently checked the axiom output. The fresh focused build completed
3443 jobs; direct source diagnostics contain only the untouched h3 `sorry`
warning. This theorem uses exactly `propext`, `Classical.choice`, `Quot.sound`,
with no `sorryAx`. Strict preservation verifies 1317 statements, 1394 frozen
commands and 43 prior Core files. Logs are in
[`cdw-validation`](../../plans/v1-s6/cdw-validation/).

Phase B remains in progress solely because the h3 bound is open. Phase C has
not started; this checkpoint makes no broader S6 acceptance claim.
