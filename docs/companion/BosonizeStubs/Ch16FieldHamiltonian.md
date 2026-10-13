# BosonizeStubs/Ch16FieldHamiltonian.lean

**Finite carrier audit.** The `A07.Letter` label has `(branch, m, creator)` and `m ∈ {1,…,M}` by construction. `signedMode` yields `+m` for a creator, `-m` for an annihilator. `gradientCoefficient` is obtained by *expanding the existing A06 forward difference*, not by introducing a spectral derivative. The value of the square is the linear evaluation of the coefficient function on **ordered pairs**, so contractions are not hidden in an inconsistent post-evaluation rewrite. Verify `normal_pair_contraction` by cases on the two creator flags. For the same species, compare the paired mode indices and apply `A06.joint_signed_current_commutator` on the actual input subspace. Across species, use `A05.rho_cross_commute`.

**Cancellation and Fourier calculation.** At fixed `x`, write `a=Δφ_right`, `b=Δφ_left` at the symbol level. Expand `(a+b)^2+(a-b)^2=2(a²+b²)` as an ordered-word identity: the `ab` and `ba` coefficients cancel separately. For each chirality, the four sign combinations of momentum indices leave two opposite-sign pairings after summing the character over `ZMod (2*h)`. The others have frequency `±(m+n)` and vanish since `1≤m,n≤M`, `0<m+n≤2M<2h`. Opposite-sign terms enforce `m=n` and produce *two* identical `rho_m rho_-m` terms after normal ordering. Each spatial sum contributes `(2*h)`; their combined coefficient is `2*(2*h) (ζ^m-1)(ζ^-m-1)/m²`. Multiplication by the dual-square decomposition gives `4*epsilon(m)` on each of the two branches. Do not treat a formal symbol cancellation as a global current CCR identity.

**Ground, reference modes, and witness.** Because `rho_-m groundKet=0` for `m>0`, the weighted error annihilates the ground ket. With `g0=epsilon(1)`, the one-mode excited ket at `m=1` is in the kernel. For a general `m`, move the only rightmost lowering mode through `rho_m groundKet` with the signed budget CCR. The nonzero scalar `m` times the nonzero ground ket also proves `rho_m groundKet≠0`; no independent cyclicity or occupation axiom is assumed. The conclusion for `m≥2` requires the **separate** hypothesis `epsilon(m)≠g0`. For a concrete gap test, `h=8`, `M=2`, `K=2`, `ζ=canonicalRoot 16`, zero charges and distinct species `0,1` give `2M+K=6≤8`, `2M=4<16`, and `epsilon(2)≠epsilon(1)`. Establish the last inequality algebraically or from the *proved* Core canonical-dispersion formula; it is a proposed theorem, not numerical verification.

**Proof dependency order.** A07 linearity/contraction → A07 chiral coefficient identity and symbol cancellation → CH16 local identity → chiral DFT collapse (character orthogonality and no alias) → weighted field on budgets → weighted error → ground/one-mode kernel → excited eigenvalue → explicit nonzero ket and concrete dispersion gap. For composite words, use `marginWithExcursion` with the budget of each right suffix, not a projection between factors.

Phase A integrated after user review. Theorems remain unproved.


Phase A finish evidence: `note/webllm/ch16/phaseA-ch16_cycle_a_be1da0fd.md`.


## Local Phase B development checkpoint

Phase A independently reviewed and accepted. Complete proof work is preserved
in [the quota checkpoint](../../../note/ch16_quota_checkpoint_2026-10-13.md)
and its candidate archive. Accepted staging statements remain unproved; the
local candidate results and dependency-blocked bodies are distinguished there.
Phase B runner acceptance and Phase C remain incomplete.


Phase B finish evidence: `note/webllm/ch16/phaseB-ch16_cycle_b_6cbdd34a.md`.
