# Ch17LuttingerModels: Phase B complete; Phase C preparation

Status: 8 proved contracts and 14 complete data declarations in this module.
All accepted proofs have fresh standard-axiom evidence. Phase B finish `f8bb8f6`:
[actual runner evidence](../../../../note/webllm/ch17/phaseB-ch17_cycle_b_0ed0c297.md).
Accepted staging source SHA-256: `d535a4cdd406507170e1b202b59dde26e9f33ca33d5f34492b6414a369e65f2e`.
Planned promoted source: [Ch17LuttingerModels.lean](../../../../Bosonize/Core/Ch17LuttingerModels.lean).
Pedagogical mapping: [corresponding reference note](../../../../notes/md/ch17_LL_Models.md).
The links use the planned `docs/companion/Bosonize/Core/` depth for migration.
The existing staged source and mathematical interfaces remain authoritative;
source hashes after import/path migration will be recorded separately.

## Exact proved declaration mapping

Every row below denotes a complete proof in `Bosonize.Ch17`. Exact
signatures, carrier instances and hypotheses are preserved in the linked source.
No historical sketch is substituted for its compiler-checked contract.

| Declaration | Realization and dependency scope |
| --- | --- |
| `zero_mode_scalar_canonical_mu` | Exact cancellation of linear charges at canonical chemical potential, including h=0 scalar conventions. |
| `luttinger_chosen_eq_bosonized` | Ambient algebraic equality for the chosen current/pairing model with exact coefficients. |
| `zero_mode_op_on_budget` | Charge observables act as specified Ns scalars on the actual joint budget. |
| `free_fermion_eq_sugawara_on_budget` | Full-band quartic antisymmetry cancellation gives a global finite identity; lowering removes modes above K, preserving the sharper frozen margin. |
| `luttinger_hamiltonian_on_budget` | Combine the free bridge, chosen-model equality and exact zero-mode action. |
| `luttinger_hamiltonian_canonical_mu_on_budget` | The preceding budget theorem with the proved symmetric zero-mode scalar. |
| `luttinger_raw_intra_on_budget` | Retain the finite Q subtraction when replacing chosen current intra-branch interaction by raw quartic interaction. |
| `concrete_luttinger_witness` | h=8,M=K=2,zero charges; two lowering currents isolate a nonzero mode-one ground pair. |

The sharp bridge preserves `K≤M` and `K+|Ns ν|<h` for the two selected species.
It does not infer the stronger legacy Core margin `2K+|Ns ν|≤h`. Instead it proves
quartic physical-creator antisymmetry and pairs all momentum-conserving terms
in the full-band raw interaction to cancel them. Combining the accepted finite
correction identity with `Q=2P−N` gives the global finite Sugawara identity.
Modes above the actual input's total excitation budget vanish by rightmost
lowering, permitting the cutoff M. Frozen Core is unchanged.

The model uses chosen current intra-branch and pairing inter-branch interactions.
The raw intra-branch theorem subtracts Q; it does not identify raw hopping with
pairing. Chemical potential cancels the linear zero-mode term exactly. The
concrete witness is not merely a nonempty budget: a local proof keeps its species
carrier abstract and applies the two branch lowering currents to isolate a
nonzero mode-one pair. It then specializes to h=8, M=K=2, zero charges, and the
actual distinct `Fin 2` branches. No physical-channel equivalence, full spectrum,
analytic continuum theory, or CH18 diagonalization theorem is asserted.

## Verification, review and Phase C boundary

All three batches completed Phase B: 37 proofs and 70 data declarations,
107 freshly audited names. The saved runner logs record warning-as-error target
compilation, only `propext`, `Classical.choice`, `Quot.sound` (or no axioms),
strict statement/data locks and CI. The deliberate verifier regression fixture's
`sorryAx` output is a negative test, not a target dependency. Historical candidate
or quota checkpoint results are superseded by these accepted batches.

Independent proof reviews were separated from authorship. Primary reviewed the
delegated A07/CH17 constructions, including the sharper free bridge and genuine
witness. `same_ccr` independently reviewed all eleven primary-authored A10 proofs;
its earlier authorship concerned the Phase A supplement, not those proof bodies.
`characters` independently reviewed the final quartic CAR proof and its bounded
resource wrapper. Author rechecks do not count as independent reviews.

Independent pedagogical review: **PASS**, `/root/joint_ccr`, 2026-10-14. The reviewer compared the three original notes as exact byte prefixes and the three original companions as verbatim historical suffixes against `be2584b`, read the accepted sources and Phase B evidence, and reviewed all seven Phase C files. Resolved findings distinguish polynomial value from coefficient, internal positive-c construction from the exported existential theorem, low-budget discard from exact-energy-shell fixation, and unweighted pairing from weighted pairing requiring nonzero mixing. The changed passages were reassessed; no deterministic findings remain. Promotion and fresh Phase C compiler/axiom/lock checks remain pending.

Phase C promotion, complete-source hashes after import migration, final promoted compiler/axiom checks and runner acceptance remain pending. The reviewed candidate is checkpointed because the live five-hour allowance reached 6%, below the formalizer 10% guard. CH18 remains outside this authorized cycle.

## Historical Phase A provenance

The complete original companion follows verbatim. Its proposed, unproved and
Phase A-only status sentences are dated historical evidence; current proof
status is the accepted Phase B record above. Its cross-module theory paragraphs
are retained for provenance rather than treated as this module's declaration map.

# Bosonize/Core/Ch17LuttingerModels.lean

### 1. Quartic Sea-Wick Ordering and the Finite Diagonal Correction $Q_{M,\nu}$
On the finite band $\Lambda^* = \mathrm{Band}(2h)$, the Dirac sea is $S_0 = \{k \in \Lambda^* : k \le 0\}$ with indicator $s_k = 1_{k \le 0}$. Defining sea quasiparticle annihilators $q_k = c_k$ ($k > 0$) and $q_k = c_k^\dagger$ ($k \le 0$), every $q_k$ annihilates the Dirac sea ket $\vert{}\Omega\rangle = \vert{}\vec{0}\rangle_0$.

For a 4-fermion word $c_{k+m}^\dagger c_k c_{p-m}^\dagger c_p$ of a single species $\nu$ with both $(k+m, k) \in \mathrm{validPairs}(2h, m)$ and $(p-m, p) \in \mathrm{validPairs}(2h, -m)$, full sea-Wick normal ordering $:c_{k+m}^\dagger c_k c_{p-m}^\dagger c_p:$ moves all $q^\dagger$ letters left of all $q$ letters in stable order with the fermionic inversion sign $(-1)^{\mathrm{inv}}$, omitting contractions. Expanding the product of sea-normal-ordered bilinears $:c_{k+m}^\dagger c_k:\,:c_{p-m}^\dagger c_p:$ via the CAR anticommutator $c_i c_j^\dagger + c_j^\dagger c_i = \delta_{ij} I$ produces:
$$
:c_{k+m}^\dagger c_k c_{p-m}^\dagger c_p: = :c_{k+m}^\dagger c_k:\,:c_{p-m}^\dagger c_p: + \delta_{p, k+m}\big[s_p t_k - (1-s_k) t_p - s_p(1-s_k) I\big],
$$
where $t_k = n_k - s_k I$. Summing over $m \in [-M, M]$ and valid band pairs $(k+m, k)$ and $(p-m, p)$, the bilinear product sum combines with the exact finite-band commutator $[\rho_{-m,\nu}, \rho_{m,\nu}]$ and the $\pm m$ contraction terms to yield:
$$
\sum_{m=-M}^M \sum_{k,p} :c_{\nu,k+m}^\dagger c_{\nu,k} c_{\nu,p-m}^\dagger c_{\nu,p}: = 2\sum_{m=1}^M \rho_{m,\nu}\rho_{-m,\nu} + \hat{N}_\nu^2 - Q_{M,\nu},
$$
where $Q_{M,\nu} = \sum_{k \le 0}(1 + 2\min(M, -k))(I - n_{\nu k}) + \sum_{k > 0}(1 + 2\min(M, k-1))n_{\nu k}$. When $M \ge h - 1$, every distance within the half-band is accessible and $Q_{M,\nu} = 2\hat{P}_\nu - \hat{N}_\nu$.

### 2. Hopping vs. Pairing Inter-branch Models
Because even-degree bilinears of distinct species commute ($[\rho_{m,R}, \rho_{n,L}] = 0$), the raw opposite-transfer inter-branch interaction (17.2) factors directly into normal-ordered density modes:
$$
H_{2,\mathrm{raw}} = \frac{g_2}{L}\left[\hat{N}_R\hat{N}_L + \sum_{m=1}^M (\rho_{m,R}\rho_{-m,L} + \rho_{-m,R}\rho_{m,L})\right].
$$
With computational creators $C_\nu = \rho_{m,\nu}$ and annihilators $A_\nu = \rho_{-m,\nu}$ ($m > 0$) on both branches, this is the number-conserving hopping interaction $C_R A_L + A_R C_L$, which annihilates $\vert{}\vec{N}\rangle_0$. The hyperbolic Luttinger pairing Hamiltonian instead requires $C_R C_L + A_R A_L$ (`pairingInterBranch`), which creates pairs of opposite-branch excitations out of $\vert{}\vec{N}\rangle_0$.

### 3. Energy-Shell Schrieffer-Wolff Decomposition
The budget decomposition $\mathcal{B}_K = \mathcal{B}_{K-1} \oplus \mathcal{H}_K$ partitions states by total excitation energy $\sum_\nu \sum_{m \ge 1} m\, n_{m,\nu}$, not by single-mode index. In particular, at $K = 2$, the repeated mode-1 state $(\rho_{1,\nu})^2\vert{}\vec{N}\rangle_0$ has excitation energy $2$ and belongs to $\mathcal{H}_2$: it is discarded by the energy-shell projection $P_1$ onto $\mathcal{B}_1$ even though it contains no mode-2 factor.

Source map addition: `bchSecondOrderPolynomial` explicitly records the algebraic coefficients of conjugation through degree two. `sw_compressed_bch_second_order` identifies its compression with `swEffectiveSecondOrder` under complementary projectors, a block-diagonal baseline, an off-block generator, and its stated generator equation. This is a finite polynomial identity; no analytic exponential or remainder estimate is asserted. `sw_2x2_exact_eigenpair` supplies a genuine nonzero eigenvector at t=2/3 with eigenvalue -1/3, while `sw_2x2_truncation_witness` supplies the distinct truncation value -4/9. The eigenpair theorem does not by itself prove that this eigenvalue is the lower one or compare with an exact exponential rotation.

Companion correction: The second-order BCH polynomial is H0+t(V+[S1,H0])+t²([S1,V]+[S1,[S1,H0]]/2). Compression removes the first-order off-block part and the diagonal-perturbation contribution to the nested bracket, leaving PH0P+tPVP+t²P[S1,V]P/2. The explicit matrix eigenvector is (-2,1), whose image under H0+(2/3)V is (2/3,-1/3)=(-1/3)(-2,1). All new theorem contracts remain unproved Phase A obligations.


### Compiler acceptance evidence

Fresh local `make verify-a` passed with Lean 4.35.0-rc4 (commit c29b6dda4f7c20e3eeaa717c4e565663c5cfa364): 70 data declarations, 37 one-sorry theorem stubs. Every audited definition has only permitted standard axioms or no axioms; there are no data placeholders. The only compiler warnings are expected theorem placeholder warnings. The transaction runner will rebuild and repeat data auditing and strict locks before accepting these sources.

### Transport repair and independent Phase A review

The external browser response `response_json.md` was preserved byte for byte; original SHA-256: `7442ccdc7973290276f4fe639ac50b618e67239bb48c9496ef0f9611c48d2056`. Its malformed JSON mixed unescaped LaTeX with differently escaped newline layers and broken single-backtick Lean fences. Local recovery separated prose and Lean transport, reconstructed readable formulas against the source notes, and writes the final envelope using a JSON serializer with the original packet ID and base SHA. No payload commands were executed.

The installed Lean compiler identified a deterministic typeclass mismatch in `highShellProj`: product equality differed from the CAR carrier's captured equality. The definition now explicitly installs `(A05.speciesOrder h).toDecidableEq`, matching existing Core; no Core changes were made.

Independent review roles: `characters` reviewed the browser-authored A07 contracts and then the locally authored A10 supplement; `same_ccr` reviewed A10 and authored that supplement; `joint_ccr` independently reviewed CH17. The requested flash/pro models are unavailable in this session, so agents used the inherited available model. Primary reviewed the final integration. All verdicts pass after the A10 coverage correction. This is interface review, not proof completion.

A07: all 18 contracts passed review of sea-word ordering, CAR contraction, finite correction weights, endpoint/full-band relation, distinct hopping/pairing models, actual adjoints and Bogoliubov constant/sign. Exact finite CAR sanity checks at h=2 found no quartic failures and verified raw=current-Q for M=0..5; these finite checks are not general Lean proofs.

A10: review found that a polynomial definition alone did not supply a truncated-conjugation theorem, and a rational inequality alone did not supply an eigenvalue witness. The supplement adds `bchSecondOrderPolynomial`, `sw_compressed_bch_second_order`, `swCounterEigenvector_2x2`, and `sw_2x2_exact_eigenpair`. An independent reviewer checked the degree-two coefficient algebra and the nonzero eigenvector (-2,1). Generic complementary projectors satisfy P+Q=1 in that contract; the ambient shell projectors instead sum to the budget projector. Apply the generic identity only on a carrier/extension where its hypotheses actually hold. No analytic exponential identity, remainder bound, or lowest-eigenvalue assertion is claimed.

CH17: all eight contracts passed review of Hamiltonian coefficients, explicit zero modes, raw-Q correction and witness nonzeroness. The sharper Sugawara bound K+|Nν|<h remains a new Phase B proof obligation; installed Core supplies only the sufficient bound 2K+|Nν|≤h. Independent finite CAR occupation checks passed 133 qualifying cases for h=1..5, without establishing a general Lean proof. The concrete h=8,M=K=2 witness meets branch margins 6≤8 and Sugawara margin 2<8, with stable velocities v1=4,v2=3. Distinct excitation degrees prevent its creator-pair terms cancelling.

The advisory `docs/stub_suggestion/` and `docs/proof_suggestion/` directories are absent. Source reconciliation used the current CH17 note, appendices A07/A10, TOC and installed frozen Core. All 37 theorem contracts remain one-sorry Phase A stubs. Definitions must pass fresh data axiom auditing before acceptance; standard axioms are `propext`, `Classical.choice`, and `Quot.sound`. Proof verification, zero-placeholder theorem auditing and promotion belong to later phases, which are outside this request.

Phase A integrated after user review. Theorems remain unproved.


Phase A finish evidence: `note/webllm/ch17/phaseA-ch17_cycle_a_fb57086e.md`.


Phase B finish evidence: `note/webllm/ch17/phaseB-ch17_cycle_b_0ed0c297.md`.


Phase C finish evidence: `note/webllm/ch17/phaseC-ch17_cycle_c_fefac95c.md`.
