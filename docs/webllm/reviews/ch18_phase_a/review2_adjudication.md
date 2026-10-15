# CH18 Phase A — Reviewer 2 adjudication (2026-10-14 20:45)

## Verdict: CHANGES_REQUIRED

- All 28 statements in candidate 1085fc8a are true, provable from the frozen Core, and have jointly satisfiable hypotheses.
- R1's B1/B2 are interface-strength/coverage gaps rather than correctness bugs. They must still be fixed before freezing, because a frozen interface cannot be strengthened without a Core migration.

**Verified Core facts:**
- `A07Interactions.oppositeOrientation` (A07 L64).
- `bogoliubovCreator`/`bogoliubovAnnihilator` (L255-265).
- `A05.rho_cross_commute (h) (ν η) (hne : ν ≠ η) (m n)` (A05 L465) is global.
- `A06.joint_signed_current_commutator` needs `|m|+|n|+K+|Ns ν| ≤ h`.

## Findings
| id | class | note |
|---|---|---|
| B1 | PERTINENT | [Ã_η, C̃_η̄] = 0 holds globally via `rho_cross_commute` plus [X,X]=0; the budgeted version's hypotheses are unused. |
| B2 | PERTINENT | [Ã_R, Ã_L]v = cs(m−m)v = 0. Budget needed (margin 2m+K+\|N\| ≤ h from `branchMargins` + `hcut`). Completes dressed CCR (Thm 18.4). |
| N1 | PERTINENT (bundle) | tanh relation; in guidance §D. |
| N2a | PERTINENT (bundle) | g = √((v1−v2)/(v1+v2)); in guidance §D. |
| N2b | DEFERRABLE | g < 1 ↔ 0 < v2; interpretation only. |
| N2c | PERTINENT | c²+s² = (g+g⁻¹)/2; used by ch19_phase_ab_design.md L40, L73 and ch19_correlations.md L56. |
| N3 | DEFERRABLE | Closed-form ΔE, positivity; c14 context only. |
| N4 | DEFERRABLE | u = √(v1²−v2²); trivial. |
| N5, N6, N12 | NOT PERTINENT | Redundant hypotheses, satisfiable; mirror the sources/Core. |
| N7 | PERTINENT (cheap) | Delete unused `vacuumShiftOp`; `concretePair` gets used via N11. |
| N8 | PERTINENT | `A08Ch18Scalars` would freeze as `Bosonize/Core/A08Ch18Scalars.lean`, upstream of the real Appendix A08. Merge into `Ch18Bogoliubov.lean`. |
| N9 | PERTINENT | `LuttingerParams` abbrev plus `toHyperbolicPair`; used by the A08 stub (L146, L149) and A09 stub (L33-34). |
| N10 | DEFERRABLE | Ground theorems for arbitrary (c,s). |
| N11 | PERTINENT (bundle) | Witness g = 1/4 and 2us² = 9 (c18). |
| N13 | DEFERRABLE | Doc-only citation. |
| **A1 (new)** | PERTINENT | Carrier-generic inverse lemma, needed by CH19 B3 / the A08 PolyCarrier. The concrete inverses are hard-wired to `A05.rho`. |

**Provability spot-checks (all OK):**
- Margins via `joint_signed_current_commutator`.
- Ground theorems via `rho_lowering_budget_zero` + `ground_mem_budget`.
- `_ne_zero` via `excited_ket_nonzero` with exactly `marginAt h M m Ns (speciesOf η̄)`.
- Oscillator/Hamiltonian identities as sums of `bogoliubov_expansion_on_budget` + `Ch17.luttinger_hamiltonian_on_budget`.
- Witness `dressedModeNumber g ≠ 0` via ⟨g,Dg⟩ = u(‖Ã_R g‖² + ‖Ã_L g‖²) > 0.
- 27π/8 checks.
- Joint satisfiability at (8,2,2,0).

Change list: see `ch18_phaseA_changes_round2.md`.
