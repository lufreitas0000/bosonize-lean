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
