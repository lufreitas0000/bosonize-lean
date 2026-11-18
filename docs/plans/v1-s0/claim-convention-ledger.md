# V1-S0 claim and convention ledger

Date: 2026-10-17. Status: proposed synthesis, pending independent review.
The checked checkout is `728987b0e939fd11a0dbfd29a8ecdc6a4368ca17`; all six reply
hashes are recorded in [`V1_REVIEW_INPUTS_2026-10-17.json`](../V1_REVIEW_INPUTS_2026-10-17.json).
The source set remains in
[`ch20-theory/`](../ch20-theory/README.md) and raw replies remain in `notes/review/`.

## Global conventions and three claim layers

| Layer | Carrier and meaning | What is established here | Boundary |
|---|---|---|---|
| I. Uncompressed oscillator and coefficientwise series | `OscAlgebra M` is `FreeAlgebra ℂ (OscGen M)`; `oscRep` represents it on the weighted polynomial carrier. CCR hold in that representation and descend inside `omegaP` expectations by contextual lemmas. | A08 proves normalized positivity, `omegaP_ccr_descends`, its `aa`/`cc` analogues, `omegaP_mul_dressed_annihilator`, and `omegaP_dressed_creator_mul`. The pull-through/Wick and vertex identities are mathematically supported proposals, not new Lean theorems. | Do not assert CCR as literal equalities in the free algebra. Coefficientwise formal `t` does not mean analytic evaluation at `t=1`. |
| II. Finite CAR and restricted comparisons | Actual occupation Fock spaces; charge sectors and total-excitation budgets; ambient products and separately compressed maps are distinct. | CH13–14 and finite CH20 contain actual shifts, fields, typed candidates and projection residuals. Exact selected current-word moments can hold on path domains. | No finite-dimensional global nonzero CCR representation; no product preservation without residual control; finite oscillator states are not automatically CAR density matrices. |
| III. Analytic/continuum | A completion, limit, or family of regulators with its own domains and estimates. | No claim in this package. | Convergence, `t=1`, continuum exponents, thermodynamic gaps, CFT/KT or RG conclusions require a separate program. |

Conventions used below: rightmost operator acts first; `[A,B]=AB-BA`; adjoints reverse products; oscillator pairing is conjugate-linear in its first input. For A08 modes, weight is `m=i.val+1`; `C` is multiplication and `A=m ∂`. The physical lattice has `L=2h`, actual band `Band (2*h)`, species twists and a joint total-energy budget, not independent per-mode cutoffs. The source/target distinction is retained for every charge-changing map.

## Q1 — Ordered Wick moments

**Precise claim.** For homogeneous linear forms `Y₁,…,Yₙ` in bare or dressed oscillator generators, set `Qᵢⱼ=omegaP(YᵢYⱼ)` in that order. The proposed recurrence is
`omegaP(Y₁…Yₙ)=Σ[j=2..n] Q₁ⱼ omegaP(Y₂… omit Yⱼ …Yₙ)`;
the shortened word retains its order. It yields zero odd moments and, for one centered linear form with `q=omegaP(Y²)`, `omegaP(Y^(2k))=(2k)!/(2^k k!) q^k`. The formal exponential identity is coefficientwise `omegaP(Exp_f(itY))=Exp_f(-q t²/2)`.

| Field | Reconciled entry |
|---|---|
| Carrier / state | Uncompressed polynomial oscillator representation; `omegaP = omega0 ∘ bogoliubovMap(c,-s)`, a normalized positive linear functional. Not a state on a finite CAR budget. |
| Algebra/order/adjoint | Use the actual free-word product order. Split forms into dressed annihilation and creation parts. Use right-annihilator and left-creator vacuum boundary identities exactly as declared in A08. `Qᵢⱼ` is bilinear, generally not symmetric. |
| Modes / budget / hypotheses | Any finite `M`, arbitrary finite word degree, unbounded polynomial degree. No lattice `h`, charge budget or CAR margin enters. `M=0`, `s=0`, either sign of `c,s`, zero forms and zero covariance are included. |
| Proof strategy / lemmas | Convert bare coefficients through the inverse Bogoliubov substitution; derive the generator contraction table; apply contextual CCR under arbitrary prefixes/suffixes; prove the pull-through recurrence by induction, then pairing factorization. Positivity establishes legitimacy and nonnegative Hermitian variance, not Wick factorization. |
| Support / counterexample | A08's actual state and contextual CCR support the recurrence. An unordered contraction rule fails already for free one-mode `omega0(ACAC)=1`; identifying `CA` with `AC` gives 2. Positive states with the same two-point data need not have Gaussian fourth moments. |
| Status / evidence still needed | **Supported proposal.** One reply derives it; it is not Lean-verified and this synthesis is not independent review. Independent review must bind the exact recurrence/table to A08's free-algebra contextual lemmas and check mixed bare/dressed fourth moments. |

The surviving result is a formal/uncompressed theorem, not a finite interacting Wick theorem. Symmetrized contractions are valid only for the fully symmetrized operator product (or commuting forms), not arbitrary ordered words.

## Q2 — Formal charge/oscillator correlators

**Precise claim.** On the auxiliary charge lattice `ℂ⁽ℤ²⁾` tensored with the uncompressed polynomial oscillator carrier, with the prompt's source-first charge words and formal central self-adjoint `t`,
`widehatω_{P,N}(W_J(t,x)* W_J(t,y)) = L⁻² ζ^(a_J(N)(y-x)) Exp_f(-2 g_J D₁(x,y)t²)`,
where `a_D=N_L-N_R-1`, `a_S=N_R+N_L`, `g_D=(c-s)²`, `g_S=(c+s)²`, and `D₁=Σ_{m=1}^M(1-cos(2πm(x-y)/L))/m`.

| Field | Reconciled entry |
|---|---|
| Carrier / state | Auxiliary bilateral charge basis tensored with polynomial oscillators; charge vector functional at the source ket tensored with `omegaP`. Neither is a physical finite-CAR density matrix. |
| Algebra/order/adjoint | Charge phase acts on the source before the shift; `K_D=F_R†F_L phase`, `K_S=F_RF_L phase`; adjoint reverses the entire product. Same-channel `X_J(x),X_J(y)` commute because opposite chiral commutators cancel. Mixed-channel commutators generally do not vanish. |
| Twists / charges / modes | The simple prompt charge convention is gauge-equivalent to, but not literally identical with, the manuscript/CH13 finite-sea sign convention. The formal sum has finite `M`; `M≤h` is not needed for the auxiliary identity but is relevant to a physical comparison. No CAR energy budget appears. |
| Proof strategy / lemmas | Derive signed-shift source phase; prove Hermiticity and same-channel commutation; derive difference variance `4g_JD₁`; use the ordered oscillator vacuum recurrence and coefficientwise formal exponential. Keep Weyl-type, bare-normal-ordered and dressed-normal-ordered vertices distinct. |
| Support / counterexample | Two replies derive the formal result and agree on the positive SC exponent. Equal-point formal Weyl product is `L⁻² I` under its algebraic product. A finite-CAR Slater calculation gives `1/4` for the corresponding physical bilinear norm square on `L=4`, versus `1/16`; this falsifies the proposed normalized physical identification, not the formal identity. |
| Appendix sign reconciliation | The reply alleging a negative SC exponent cites a stale/different snapshot. Current local Appendix A08, §“Formal vertices and coefficientwise evaluation”, and Section 20.2, equations `ch20b-sc-corr` and `ch20b-coefficients`, both use `+(N_R+N_L)(y-x)`. No source formula correction is justified. |
| Status / evidence still needed | **Supported proposal** at the formal layer; not Lean-verified. Freeze only after independent review resolves the gauge adapter, the charge functional and all formal-series conventions. Physical interpretation remains a separate obligation. |

The prefactors are convention-dependent. Dressed normal ordering multiplies a vertex by `Exp_f(g_J H_M t²)` and gives a two-point scalar exponent `2g_J(H_M-D₁)t²`; bare normal ordering instead uses `Exp_f(H_M t²)` and gives `(2H_M-2g_JD₁)t²`. These do not license changing the physical CAR field normalization.

## Q3 — Physical finite field dictionary

**Precise claim under test.** The CH14 actual field is the typed map `physicalMap : B(N,K_in) → B(N-e_ν,K_out)` built from the twisted Fourier annihilator and target projection. Its candidate is the ordered finite polynomial `vertexCandidate`: source zero-mode scalar, projected Klein lowering, `wPlus` Taylor, typed cutoff transition, then `wMinus` Taylor. CH14 proves equality only under full-vector ground equality, cyclicity, and the two common-residual recurrences.

| Field | Reconciled entry |
|---|---|
| Carrier / state | Actual finite CAR occupation carrier; joint charge and total-energy budget. Ground vector is the actual `groundVector`. Candidate moves first to the lowered-charge target sector. No oscillator state is substituted for the physical ground vector. |
| Operator convention | `wPlus=Σ_{m=1}^M ζ^(mx) rho(-m)/m` is the lowering part; `wMinus=-Σ_{m=1}^M ζ^(-mx) rho(+m)/m` is signed raising. `wPlus†=-wMinus`; `wMinus†=-wPlus`. `physicalMap` uses twisted single-particle annihilation with normalization `L^(-1/2)`. |
| Charge/twist/order | `physicalMap` lowers charge by `e_ν`; CDW and SC bilinears have shifts `(+1,-1)` and `(-1,-1)`. `zeroScalar` uses the external twist lift and the **source** charge phase before the Klein shift. Candidate factors act right-to-left as specified above. |
| Full ground image | A08/CH14 exposes `physical_ground_expansion`: a sum over every occupied momentum, with the CAR removal sign and actual twisted character, followed by the full target projection. It is not determined by the selected ground-to-ground coefficient. A finite-M candidate generates only the retained current-partition image. |
| Margins / discarded channels | `A05.r2(h,K,N)` and CH13 `pairMargin` support exact current/partition actions and Klein-kernel ground reproduction in source and shifted sectors. They do not prove full physical/candidate ground-vector equality, cyclicity of an arbitrary chosen generator family, or equality of the physical and candidate recurrence remainders. `projected_recurrence_residual` retains both source and target excursions. CH20's `concrete_discarded_channel_nonzero` proves an actual nonzero intermediate channel. |
| Status / conclusion | **Contradicted proposal** for unconditional/global identification of these exact candidates as physical fields; use a corrected restricted or controlled comparison. The hypotheses of CH14 are sound and remain unresolved for nontrivial physical specializations. See [dedicated analysis](physical-field-dictionary.md). |

## Q4 — Finite interacting states and comparison with `omegaP`

**Precise claim under test.** A nonzero finite budget with a specified Hermitian compressed Hamiltonian has a positive normalized ground-state density matrix by finite-dimensional spectral theory. This does not identify it with the polynomial state. A universal simultaneous compressed dressed-annihilator vacuum is false for the cited three-dimensional example. Selected comparison moments may match or differ, depending on the specified dictionary and state.

| Field | Reconciled entry |
|---|---|
| Carrier / state | `H_B = i† H_F i` on a nonzero actual budget `B(N,K)` is Hermitian. Its lowest spectral projection `Q₀` gives `Γ₀=Q₀/Tr(Q₀)` and `ω_B(O)=Tr(Γ₀O)`. A ground state of `H_B` need not be a ground state of ambient `H_F` unless the budget is invariant or additional spectral conditions hold. |
| Order / budgets | Compression is not multiplicative: `Comp(AB)-Comp(A)Comp(B)=i†A(1-P)Bi`; source/intermediate/target versions retain the same ordered residual. A word can leave a budget and return. Do not infer every high moment vanishes just because one intermediate energy exceeds `K`. |
| High-moment claim | For the special monotone word `(rho(-m))^q`, an annihilation-side vanishing claim requires the exact `rho_budget_map`/lowering hypotheses at every step and the actual source charge/band margins. Then compare the ambient word evaluated in a state supported on the budget. A bare `q m>K` inequality is not a universal proof without those path facts. The polynomial counterpart `omegaP(C^q A^q)=q!(m s²)^q` is positive for `s≠0`. Do not apply the argument to words whose right-to-left path includes raising before lowering. |
| `h=8` example | The eight total-energy partitions through `K=2` are: vacuum; two mode-1 states; four energy-2 states from `(2,0),(0,2),(1,1)` at mode 1; and two mode-2 states. Under current actions and `α=2π/L=π/8`, the compressed block on `{Ω,C_R1 C_L1 Ω}` is `α[[0,15],[15,34]]`; the other six states have energies `17α` (two singletons) or `34α` (four states). The unique ground eigenvalue is `α(17-√514)` and vector is `(Ω-η|11>)/√(1+η²)`, `η=15/(17+√514)`. Its two stated moments are `(1-17/√514)/2` and `-15/(2√514)`, while `omegaP` gives `9/16` and `-15/16`. This derivation is internally checked against the stated basis and pairing-mode action but has not been independently reviewed or proved in Lean. |
| Status / evidence still needed | **Supported construction** for finite spectral state; **contradicted** universal finite squeezed-vacuum/all-moment identification. Independently review the matrix entries, exact source current convention and relation to `H_B`; then derive parameterized comparison/obstruction. |

The small matrix is a nonvacuity/falsification witness only; it does not prove a parameterized theorem.

## Q5 — Algebraic duality and finite-CAR symmetry

**Precise claim under test.** On the uncompressed algebra, a right-oscillator sign reversal paired with `s→-s` exchanges `g↔g⁻¹`. Charge reflection must be written in a fixed Klein gauge. Separately, a proposed left particle-hole unitary with momentum reflection/complementation may act on finite CAR; it is not automatically the formal oscillator map.

| Field | Reconciled entry |
|---|---|
| Carrier / state | Formal map acts on oscillator/charge algebra and transports the family `omega_{P,N}` to a reflected parameter/charge family. Finite candidate acts on full finite CAR occupation Fock space or explicitly typed budget sectors. |
| Order / adjoints / phases | Star map preserves order; it is not an anti-automorphism. `K_D,K_S` transform with an extra sign under the simplified gauge and bare `U_r`; a phased/gauge-adjusted reflection changes the displayed sign. Current manuscript convention is the canonical reference; derive the diagonal charge rephasing before translating. |
| Finite map / twists | The reply's candidate `k→1-k` plus left occupation complementation preserves charge reflection and excitation budgets under its exact band convention. Boundary twist determines the position-dependent phase; the current centered antiperiodic twist can cancel it. The claimed finite current Hamiltonian covariance includes the residual `(2μ-2πv_F/L)N_L`. |
| Distinction / obstruction | Formal map negates right oscillator generators; particle-hole candidate negates nonzero left finite currents and changes zero density by `LI-ρ_L(0)`. A one-right-particle relation `T₁²=T₂≠0` obstructs a global unitary that negates both `T₁,T₂` while preserving that charge sector. These are not the same map. |
| Status / evidence still needed | **Supported proposal** for the formal gauge-explicit family covariance; **unresolved proposal** for the distinct finite construction and its full physical theorem. Independent review must check the finite permutation signs, twist, Hamiltonian residual and all map claims. Scope is conditional; no physical unitary follows from `g↔g⁻¹`. |

## Q6 — Controlled finite comparison

**Precise claim under test.** A free-word substitution by actual finite density currents can reproduce `omegaP` on a selected bounded word family when exact right-suffix paths satisfy current/Haldane margins and the inverse Bogoliubov substitution is applied to observables. Separately, a physical product comparison is `P_t A B P_s = P_t A P_m B P_s + R`, `R=P_t A(1-P_m)BP_s`; norm estimates require common carriers and explicit field/state defects.

| Field | Reconciled entry |
|---|---|
| Carrier / state | Word comparison: actual finite CAR sea and charge sector, with uncompressed polynomial word evaluator. It is not an interacting-ground-state comparison. Product comparison: three explicit actual budget carriers or a common verified Haldane image. |
| Order / path | Read words right-to-left. For every expanded word after `β⁻¹`, track the exact cumulative mode-energy changes along each nonzero suffix/path, including charge labels and target restrictions. A path may exit then return; only a factorwise path theorem justifies word equality. |
| Modes / margins | Total weighted degree, not a Cartesian tensor cutoff. `M≤h` is not by itself a sufficient word margin. The proposed `2 d M+|N_ν|≤h` is conservative only if derived from all needed source/intermediate/target Core hypotheses; it is not accepted merely because it appears in a reply. If `M<E`, the Haldane map may be an embedding, not onto. |
| Error decomposition | Keep intermediate projection, omitted-mode/range, normal-ordering, state, and dispersion errors separate. Do not subtract operators on different spaces. A triangle inequality with unknown errors is not quantitative control. |
| Nonvacuity / counterexample | CH20's four-site discarded channel is nonzero for a specified source/intermediate/target. Same-species finite-cutoff sine exchange need not equal a continuum sawtooth. The formal equal-point normalization differs from a finite CAR example. |
| Status / evidence still needed | **Supported target** as a family of conditional finite theorems; precise suffix/path hypotheses remain unresolved. Independent review must derive an exact bound from CH07/09/11/13 source declarations; no coarse bound is frozen. |

## Findings and next actions

1. **Confirmed:** current Appendix A08 SC phase is positive and agrees with Section 20.2; no formula edit.
2. **Confirmed:** CH14 equality is conditional; a full field image and common residuals are required. Numerical margins do not entail them.
3. **Confirmed obstruction:** finite projection product residual is nonzero in the accepted finite CH20 witness. Preserve it.
4. **Supported, not accepted:** ordered Wick recurrence and formal coefficientwise correlators.
5. **Unresolved:** exact suffix-path current theorem, general interacting state comparison, finite particle-hole implementation, and A10-to-CH21 restricted application.

Next actions: an independent reviewer must review this ledger and the companion field analysis against the exact source hashes; the human must resolve the two optional scope choices listed in the [completion contract](completion-contract.md). Do not freeze or implement an interface until both gates are resolved.
