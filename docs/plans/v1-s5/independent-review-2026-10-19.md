# S5 independent review record — 2026-10-19

Reviewer: native agent `/root/s5_review`, read-only, independent of source
authorship. One reviewer at a time under the user's sprint authorization.
No paid provider, Antigravity or unrelated chat was used.

## Phase A — PASS for scoped initial locking

The initial review requested an explicit complete-spectrum contract: the
matrix action and ground minimum did not expose all spectral multiplicities.
Resolution: added `smallEigenvalue` and `small_spectral_basis`, with a complete
orthonormal eigenbasis and the eight indexed eigenvalues. Also added the direct
ground-state raw-moment obstruction corollary. The reviewer rechecked both.

| Approved artifact | Exact SHA-256 |
| --- | --- |
| `BosonizeStubs/V1S5FiniteGroundState.lean` | `3e80a8070a031cbea4d3b695866e38ba7e50382a69b61383a93ecabf9cb0d7a5` |
| `BosonizeStubs/V1S5MomentObstruction.lean` | `00a56f307fa5fa43826933d715f0e39511cf60a35c7c660ae4786d2b1fce704a` |
| `BosonizeStubs/V1S5SmallInteractingModel.lean` | `2e62891f3ab8c60f8c5fcd4bc4680418c08fd9a0cd30906c3e21e4d01ed946ca` |
| Reviewed companion | `7377ce26007b10397a86dc4cff3dd5dacf4db1b5de47464cca0655d6f94b5814` |

The reviewer checked the actual pairing Hamiltonian, full zero-mode operator,
current-normal-order conventions, budget/carrier, Rayleigh minimum, state
positivity and normalization, raw moment dictionary, both compression
placements, lowering floor, complete small model and proof feasibility.
It independently reran the sandboxed data audit: all 19 data declarations use
only permitted standard axioms, with no `sorryAx`. The supplied scoped build
passes; 32 theorem placeholders remain, plus the proved admissibility witness.

An earlier elaboration diagnosis verified that explicit scalar and carrier
arguments resolve generic subtype/adjoint inference. No custom instance,
carrier change, operator substitution or mathematical weakening was needed.

Approval covers exactly the three S5 initial interface records, preserving all
earlier records and complete Core sources. This is not proof completion,
promotion or pedagogical acceptance.

## Later gates

Phase B final proof review: pending. Phase C migration and pedagogy: pending.

## Scoped Phase B interface amendments — PASS

The same independent reviewer approved the two redundant finite-dimensional
binder omissions, local inclusion/witness elaboration resource settings, and
module-system source split. Exact-source review compared parsed declarations
against `803bdf9`: all 19 original data definitions remained unchanged, and all
33 prior theorem conclusions/headers remained except the four approved local
prefixes. Additions are exactly `submodule_inclusion_adjoint`, `smallLabel`,
`small_label_bijective`, and `small_partition_state`. Only the four S5 records
were migrated/amended; unrelated records and Core bytes remain unchanged.

Exact-source review hashes (before subsequent proof-body integration): Ground
`f199317a26ccb54d4fcd881279fe84c59916980bce5307f95373f332f8850d8b`;
Vector `1e534841bcfa89f905b3bde1dd2ed353455963fe66377256c7db5db55e079db4`;
Moment `e837637121941a680d3dbbe86f54d929f213364104f2bba25e0a457b6fd1d003`;
Small `bf64ae5b919892a08f89e6103e9cfc021c7cf359c06335ecf0ee00f133a6d4db`.
Current checkpoint hashes are recorded separately in `checkpoint-hashes.json`.
The fresh four-target build passes with 10 explicitly unproved contracts.
Full post-amendment axiom audit and independent final proof/pedagogical reviews
remain pending. This approval is not Phase B or Phase C completion.


## Resumed helper amendment — 2026-10-19

Independent reviewer `/root/s5_review` approved exactly two proved additions:
`compression_inner` (arbitrary finite Hilbert carriers, actual adjoint pairing)
and `small_eta_algebra` (five scalar identities, including both moment ratios).
Exact assembled SHA256: VectorStates
`6f6196400fc88f2aef76be649f27fbc36e4f99ac9063ed42bd8966791288a635`;
SmallInteractingModel
`44d0e5475be66b56b0e4536ade0a5286cc8b219ddbe97edcddec6983a9c222de`.
Git diff checked: exactly two additions, 29 lines; old declarations unchanged.
Sandboxed target build completed (3441 jobs), with only seven preexisting
small-model placeholders. Fresh audits of both additions and the preceding
`current_word_lowering` / `small_current_lowering` helpers use only
`propext`, `Classical.choice`, `Quot.sound`. Only the two affected S5 statement
lock records are amended. This is not Phase B completion or promotion.


## Final staging proof review — 2026-10-19

Native read-only reviewer `/root/s5_review` approved the two additional generic
rotation/diagonalization helpers, including the explicit lowest-vector identity,
and the three scoped small-model resource prefixes. No definitions or original
conclusions changed. Complete mathematical/proof review PASS is conditional on
fresh full compilation, all 64 declaration axiom audits, strict locks and Core
preservation. Source hashes at review:

- Ground: `f199317a26ccb54d4fcd881279fe84c59916980bce5307f95373f332f8850d8b`.
- Vector: `2b1b6ce7eb6694abae1094a93a40b37bfb1cfedb7b659f4a702ce3c851f07822`.
- Moment: `66d660acf1b08fee021260b6b038f070c0f32aff887e9f9db8656bb89f85aad9`.
- Small: `3a97db5f0ca34e061a0f2e330505da3cf889a1007a884fcd30daddcbf7467c2d`.

The reviewer checked actual Chapter 17 compression, budget-wide minimality,
positive normalized extension, separate ambient/compressed lowering powers,
all eight matrix columns/eigenvalues, final-only compressed selected moments,
and the fixed S1/S4 dictionary. No mathematical blockers were found. Scoped
promotion plan approved: four moves, three staging dependency import changes,
four aggregator imports and four new Core hashes, preserving all 39 old ones.
These review verdicts alone establish neither Phase B nor Phase C acceptance.


### Final linter cleanup and pedagogy draft

The reviewer rechecked Small SHA256
`a2a43e40d1bb6b4147fe4b5cc036d2f5b1eddd84afad1d8c8f6955621c3d4755`:
exactly one unused simp argument removed and the final tactic sequence
parenthesized. The earlier full proof verdict applies to this surgical cleanup.
All 64 declaration audits report only standard axioms. Final clean-source build
is recorded in the Phase B receipt when complete.

The corrected additive pedagogical draft is saved as
`pedagogical-addition-reviewed.md`, SHA256
`02ec94473e4b0ee3f1e2c8376c419370816af3f11e19cc742f7bb4d06e4986e4`.
Reviewer PASS after correcting the complete-basis sentence and spelling out the
four square-root normalizations. It has not been appended to the chapter;
actual append preservation and promoted links remain Phase C gates.


### Checkpoint rollback clarification

The proposed linter cleanup failed compilation (`No goals to be solved`).
It was not accepted. Small was restored exactly to reviewed SHA256
`3a97db5f0ca34e061a0f2e330505da3cf889a1007a884fcd30daddcbf7467c2d`
from `52e49d4`. Its full build passes with two linter warnings, and all 64
compiled declaration audits pass. Thus the original conditional mathematical
PASS remains applicable, while zero-warning Phase B acceptance and Phase C
remain pending. No final clean-build PASS is claimed for the cleanup hash.

## Phase B final acceptance after resumed validation

`/root/s5_review` recomputed all four exact source hashes, inspected the
successful 3442-job clean build, and independently parsed all 64 fresh axiom
audit entries. Final Phase B review PASS: all original contracts proved, no
mathematical findings outstanding. Small SHA256 is
`0cb8ddf52321d9141728fbbea05bfd9152500de702280baa95395865952dfba4`;
the other three hashes are unchanged. The surgical cleanup now uses closing
alternatives and compiles with zero warnings. Strict v2 locks and preservation
of all 39 preexisting Core sources pass. See the Phase B acceptance receipt.
This closes the earlier conditional review, not the subsequent Phase C gates.
