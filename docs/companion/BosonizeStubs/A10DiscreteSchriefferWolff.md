# BosonizeStubs/A10DiscreteSchriefferWolff.lean

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


## 2026-10-14 Phase B continuation checkpoint

11 standard-axiom theorem proofs; 0 original stubs remain; 0 contracts still depend on sorryAx. Source SHA-256: `b77a079f426943fa6fb5609316dfdb645371c88c48be82875ad480094990594c`. Fresh combined compiler exits 0 with only two placeholders across all three modules; A10 separately passes warning-as-error for all declarations. Definitions/interfaces/Core unchanged. This is not runner acceptance. Exact remaining goals, evidence and resumption sequence: `note/webllm/ch17/phaseB-checkpoint-2026-10-14.md`. Phase C remains authorized but unstarted.
