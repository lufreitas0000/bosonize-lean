# Chapter 12 Phase A independent review — 2026-10-11

Reviewer: `/root/ch11_gram_probe`. Author: `/root/ch12_phase_a`. Flash/Pro tiers are unavailable; review and drafting use the inherited available model as the authorized fallback.

## Verdict and exact reviewed snapshot

**PASS for mathematical contracts and source fidelity** on the complete final draft:

- `BosonizeStubs/Ch12Sugawara.lean`: SHA-256 `948bd05acb85135c72a120ee4bd12daa3e3ebffaaf67715b27f8487002ca46e9`.
- `docs/companion/BosonizeStubs/Ch12Sugawara.md`: SHA-256 `9d200db2284b114f2aab29e6b1580787cfb86fc4c8285935bfefad190a512813` at review. Subsequent additions of compiler/checkpoint evidence require accurately refreshed provenance.

The complete source has 26 theorem contracts, three defined operators and two carrier abbreviations. Every theorem remains a Phase A obligation with exactly one placeholder. No proof completion or Phase C status is inferred from elaboration. The reviewer made no source, lock or Core edits.

The final interface removes redundant positive-part premises from `density_bilinear_word`, `positive_word_weight` and `sugawara_word_eigenvalue`, and removes positive n from the natural raising wrapper. All are mathematically valid extensions to the zero cases. Positive parts remain essential to actual partition indexing and the CH11 positive Gram statements, which are unchanged.

## Carrier, ordering and cutoff contracts

The carrier is the actual finite complex occupation Hilbert space from Chapters 7–11; endomorphism multiplication is composition. The Sugawara definition is literally the sum of rho_m rho_(-m) for 1≤m≤M, so the lowering current acts first. The adjoint and quadratic-form contracts describe actual Hilbert adjoints. Each summand is A†A for A=rho_(-m), giving the stated nonnegative quadratic-form identity without an invented state or CCR certificate.

Ground annihilation and inactive-mode vanishing follow from the existing lowering/negative-budget grading contracts. Cutoff stability for M≥K imposes no extra R2 or upper-M restriction. This matches Chapter 12 and the repaired A04 reference: modes m>K vanish on the right before current pull-through, even when the operator sum extends beyond the band or beyond K.

For active modes, the bilinear word contract retains 0<m≤K, actual sector ground and total word energy≤K. R2 supplies each actual right-remainder margin, as established in CH11. Restoring an erased matching occurrence uses globally commuting nonnegative currents; absent modes have zero multiplicity and need no membership premise. The natural list counting identity omits zero parts legitimately because their weight is zero.

The frozen CH11 lowering/count helper still assumes positive parts. The final companion correctly records that arbitrary natural lists require a local zero-entry extension using the globally commuting number current, rather than falsely claiming that frozen helper directly accepts zeros. The earlier checked feasibility pull-through for arbitrary natural lists provides a supported proof route; no frozen Core alteration is authorized or needed.

## Equivalence and commutator dependencies

Partition eigenvalues specialize actual word action and exact partition energy. The separate diagonal exact-energy action identifies the same eigenvalue for `Ch07.excitationObservable`. Whole-budget equivalence extends their agreement across the already proved actual CH11 budget partition basis. It does not use the desired Sugawara commutator to prove equivalence.

The signed commutator contract has genuinely separate source K and target J margins and requires K+n≤J with both budgets covered by the cutoff. Existing rho_n grading puts the output in the signed shifted budget; monotonicity embeds it in B(N,J), even when K+n is negative. Applying equivalence to the source and shifted output, together with global excitation covariance, proves the intended sign [H_sug,rho_n]=n rho_n. The natural wrapper uses J=K+n and validly includes n=0. No ambient global scalar current identity is claimed.

## Integer and physical energy dictionaries

The relative integer Hamiltonian is the existing same-sea shifted Hamiltonian. On fixed charge N it is excitation plus `groundEnergy N`. The complex polynomial bridge uses the proved exact integer divisibility of N(N+1), including negative charges; the target remains N(N+1)/2, not N²/2.

The new physical relative operator subtracts the actual energy of the same frozen sea at real offset β. Expanding the existing physicalHamiltonian gives the integer shifted Hamiltonian plus βN on a fixed-charge budget. Subtracting the matching physical ground polynomial cancels β globally in the excitation observable. Neither the physical relative nor absolute Hamiltonian is declared offset-independent. The companion retains the matching CH06Ext angle-twist/Fourier dictionary and does not change sea conventions or introduce an analytic limit or physical unit factor.

The physical Sugawara budget identity is therefore excitation equivalence plus the exact charge-dependent physical ground energy. All carriers and source/target budgets agree with the existing eighteen-module frozen Core chain.

## Nonvacuity

Both witness contracts request actual nonzero vectors and nonzero operator output, rather than merely a nonempty subspace. For the excited witness, rho_m applied to the sea is nonzero by the independently proved CH09 sea norm; grading gives membership, and the Sugawara eigenvalue is the positive m. For the commutator witness, the sea belongs to B(0,0), rho_n sea is nonzero, and the enlarged-target identity gives nonzero n rho_n sea. For example h=2, K=M=m=1 satisfies the excited hypotheses, and h=2, M=n=1 satisfies the commutator hypotheses. These are feasible nonvacuous contracts, not new proofs completed during review.

## Quota checkpoint and remaining validation

The final live allowance check returned five-hour used91% (remaining9%), weekly used14% (remaining86%), five-hour reset Unix timestamp1791742313. This crossed the unchanged <10% five-hour guard. The reviewer stopped new proof/compiler work and saved this essential completed mathematical-review checkpoint. No paid or reset credits were consumed.

The author supplied earlier elaboration, data axiom and native Lean diagnostic evidence in the companion; final post-cleanup validation must be tied to the exact final SHA above. Reuse any already-completed final build/data-audit logs, accurately record their outcome, and otherwise finish those checks after fresh quota recovery. Only then establish the reviewed lock and transition to Phase B. This report approves the mathematical interface; it does not bypass the final exact-source validation, quota gate or automatic A–B–C review requirements. The whole-project goal remains active and incomplete.
