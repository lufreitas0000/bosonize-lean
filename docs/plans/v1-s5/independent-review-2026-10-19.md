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
