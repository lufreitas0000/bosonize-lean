# CH18 Phase A — Reviewer 1 report (2026-10-14 20:36)

Candidate: `docs/webllm/drafts/ch18_cycle_a_6c99dd27.md` (agentctl attempt 1085fc8a, commit ae45854; api-pro draft 995b1499 + api-fast `noncomputable` repair).

## Verdict: FAIL (2 blocking)

Everything else was judged sound: signs, the 2h normalization, budgets, the witness, and the `HyperbolicPair` interface. The reviewer checked against frozen Core A07 (L68-77, L255-272, L1120-1227), Ch16 (`excitedKet`, `excited_ket_nonzero` needs `marginAt h M m Ns (speciesOf η)`), Ch17 (L37-60, L120-147, L384-400), A06 `marginAt`/`branchMargins` (L49-55), and A05 `rho_lowering_budget_zero`/`ground_mem_budget`. It also checked runner module splitting (later modules auto-import earlier ones).

## Coverage
- c01 ✓
- c02 ✓ (provable: flip (c,s)→(−c,−s); c≠0 since c²=1+s²)
- c03 MISSING (N1)
- c04 PARTIAL (N2)
- c05 PARTIAL (N4)
- c06 ✓
- c07 ✓ (Core `bogoliubov_creator_adjoint`)
- c08 ✓ (4 global inverses)
- c09 ✓ cited
- c10 PARTIAL/WEAKENED (B1, B2)
- c11 ✓ cited
- c12 ✓
- c13 ✓
- c14 PARTIAL (N3)
- c15 deferred, justified
- c16 ✓
- c17 ✓ caveats
- c18 ✓
- c19 deferred, justified

## Per-theorem
All 28 statements were judged F1/F2-sound **except**:
- #19 `bogoliubov_cross_annihilator_creator_on_budget`: F1 weaker than the global claim; F2 because `hh`, `hm`, `hcut`, `hmargin` and `hv` are all unused (the identity holds globally via `A05.rho_cross_commute` plus [X,X]=0).
- Minor redundancies: #11 `hv1` (implied by hp); #27 `hdressL` and the right half of the margin; #20 `hm`.

Back-translations were verified for the following:
- **Inverses:** (c²−s²)ρ.
- **Oscillator identity:** H_osc v = (2π/2h)Σ dressed_m v − ΔE v, with ΔE = (2π/2h)Σ2us²m.
- **Hamiltonian identity (18.11):** H_chosen v = dressed v + (E_zero−ΔE)v.
- **Ground annihilation:** Ã_R|N⟩₀ = s·ρ_{m,L}|N⟩₀.
- **Obstruction:** Thm 18.8(i).
- **Witness:** at (8,2,2,0), ΔE = 27π/8, 2M+m+|N| = 6 ≤ 8. The dressedModeNumber of the ground state is nonzero.

## Data
All are correct and tied to 2h; `concreteParams` checks numerically; nothing is named K. `vacuumShiftOp` and `concretePair` are unused (N7).

## Downstream
A08 compatible: `Ch18.HyperbolicPair` reaches it through transitive import. Caveat: the A08/A09 stubs also use `Ch18.LuttingerParams v1 v2` and `lp.toHyperbolicPair` (N9).

## Blocking
1. **B1, `bogoliubov_cross_annihilator_creator_on_budget` (F1+F2).** Restate globally for arbitrary η with no budget or margin hypotheses: `A02.commutator (bogoliubovAnnihilator h m c s branches η) (bogoliubovCreator h m c s branches (oppositeOrientation η)) = 0`.
2. **B2, missing `[Ã_R, Ã_L] v = 0` on budget (coverage c10).** Add `bogoliubov_cross_annihilator_annihilator_on_budget` with the hypotheses of #20 (`hh`, `hm`, `hcut`, `branchMargins h M K Ns branches`, `v ∈ jointBudget h Ns K`). It is true: cs([ρ_{−m,R},ρ_{m,R}] + [ρ_{m,L},ρ_{−m,L}])v = cs(m−m)v.

## Non-blocking
1. **N1:** `tanh_relation_of_params : v2*(c²+s²) = v1*(2cs)`.
2. **N2:**
   - `luttingerG_eq_sqrt : luttingerG (ofParams hp) = √((v1−v2)/(v1+v2))`;
   - `luttingerG_lt_one_iff : luttingerG < 1 ↔ 0 < v2`;
   - `c²+s² = (g+g⁻¹)/2` (needed by the Ch19 design).
3. **N3:**
   - `vacuumShiftScalar` closed form (2π/2h)(v1−u)·M(M+1)/2;
   - `0 < ΔE ↔ v2 ≠ 0` (h>0, M≥1);
   - `0 ≤ 2us²`.
4. **N4:** `hp.u = √(v1²−v2²)`.
5. **N5:** drop the redundant `hv1` in `u_lt_v1_of_v2_ne_zero`, or document it.
6. **N6:** `hdressL` is redundant in `no_common_bare_dressed_vacuum` (acceptable as a symmetric statement).
7. **N7:** `vacuumShiftOp` and `concretePair` are unused. Remove them or use them.
8. **N8:** module `BosonizeStubs/A08Ch18Scalars.lean`. The A08 prefix collides with appendix A08 (States and Correlations). Rename to `A07Ch18Scalars` or merge into `Ch18Bogoliubov`.
9. **N9:** add `abbrev LuttingerParams v1 v2 := A07Interactions.HyperbolicParams v1 v2` and `LuttingerParams.toHyperbolicPair := HyperbolicPair.ofParams` (the A08/A09 stubs use them).
10. **N10:** `dressed_annihilator_ground_*` could take arbitrary c, s (optional).
11. **N11:** the witness could optionally state `luttingerG concretePair = 1/4` and `2us² = 9`.
12. **N12:** `hm` is superfluous in #20 (harmless).
13. **N13:** the source map should cite `bogoliubov_creator_adjoint` for c07.