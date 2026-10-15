# Review warnings register

Non-blocking findings from independent reviews. Each one is either resolved by a stated deadline or escalated. Blocking findings are never recorded here: they are fixed before freezing.

| id | chapter/phase | finding | needed by | resolve by | status |
|---|---|---|---|---|---|
| CH18-N2b | CH18 A | `luttingerG < 1 ↔ 0 < v2` not stated (physical interpretation of repulsion) | none found | CH18 Phase C (prose) or optional lemma | resolved 2026-10-15 (Phase C remark 18.5a) |
| CH18-N3 | CH18 A | Closed-form ΔE = (2π/2h)(v1−u)M(M+1)/2; `0 < ΔE ↔ v2 ≠ 0`; `0 ≤ 2us²` not stated | none found (c14 context) | CH18 Phase C (prose) | resolved 2026-10-15 (Phase C remark 18.6a) |
| CH18-N4 | CH18 A | `hp.u = √(v1²−v2²)` not stated (trivial from `u_sq`, `u_pos`) | none found | optional | open |
| CH18-N5 | CH18 A | `u_lt_v1_of_v2_ne_zero` carries redundant `hv1` (implied by hp) | — | accepted (mirrors ledger c06) | accepted |
| CH18-N6 | CH18 A | `no_common_bare_dressed_vacuum` carries redundant `hdressL` | — | accepted (symmetric Thm 18.8 form) | accepted |
| CH18-N10 | CH18 A | `dressed_annihilator_ground_*` could be stated for arbitrary (c, s) | none found | optional | open |
| CH18-N12 | CH18 A | `hm` unused in the cross commutator budget lemmas | — | accepted (Core signature consistency) | accepted |
| CH18-N13 | CH18 A | Source map should cite `A07Interactions.bogoliubov_creator_adjoint` for c07 | — | CH18 Phase C | resolved 2026-10-15 (cited in notes and companion) |
| CH18-N14 | CH18 A | Design/Review prose says "every operator theorem is budgeted"; the inverse transforms and `bogoliubov_cross_annihilator_creator` are global, and `inverse_combination` is carrier-generic | — | CH18 Phase C (pedagogical sync) | resolved 2026-10-15 (global vs budget classification in notes) |
| CH18-N15 | CH18 A | Companion notebook lacks tasks for `tanh_relation_of_params`, `luttingerG_eq_sqrt_of_params`, `luttingerGInv_eq_inv`, `hyperbolic_coeff_eq_luttinger`, `inverse_combination`, `bogoliubov_cross_annihilator_annihilator_on_budget` | Phase B tracking | CH18 Phase B start (companion update) | resolved 2026-10-15 (companion tasks added) |
| CH18-T1 | CH18 sources | Transcript defects: GIA22:67 garbled; ML (4.7)–(4.13) missing; ML:1401, 1407, 1413 garbled exponents | anything citing those equations | before citing (check PDFs) | open |

Review trail for CH18 Phase A:
- Reviewer 1: FAIL (B1, B2).
- Reviewer 2: adjudication, CHANGES_REQUIRED (adds A1).
- Revision round 2: `gpt-5.4`, re-emitted by `gpt-5.4-mini` byte-identical except one blank line.
- Reviewer 1 round 2: PASS.

Records are under hub `.agentctl/reviews/`, mirrored in `docs/webllm/reviews/ch18_phase_a/`.
