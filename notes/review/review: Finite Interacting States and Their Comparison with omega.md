# Independent Mathematical Review: Finite Interacting States and Their Comparison with \\(\omega_P\\)

Bosonize-Lean, Version 1 — Chapter 19/20 state-carrier problem

Reference baseline: `40dea8bfbdc849417c072e490480d4f72536116a`, October 17, 2026.

## 1. Verdict

The state-carrier obstruction has an exact finite-dimensional resolution, but it does not establish equality between the physical interacting state and the polynomial Gaussian state \\(\omega_P\\).

The strongest defensible conclusion is:

> Every nonzero finite budget space equipped with a specified Hermitian compressed Hamiltonian admits a normalized positive ground-state functional. No dressed-annihilator vacuum equations are needed. Comparison with \\(\omega_P\\) requires an explicitly defined observable map and is generally valid only for selected moments, potentially with nonzero errors.

There are three mathematically distinct constructions:

| Approach                  | What exists                                                                                   | What it establishes                                                                                               |
| ------------------------- | --------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------- |
| (a) Spectral ground state | A density matrix supported on the lowest eigenspace of the compressed interacting Hamiltonian | An actual physical interacting state, unconditionally once the Hamiltonian is specified                           |
| (b) Transported state     | A positive normalized state obtained through a unital positive map or a suitable isometry     | An exact state comparison on explicitly related observables, without automatically relating ground states         |
| (c) Selected moments      | A finite collection of values calculated from \\(\omega_P\\)                                  | An exact algebraic reference for comparisons and estimates, without asserting a full CAR–CCR state identification |

All three are available algebraically without constructing an infinite-dimensional Hilbert completion. Only (a), however, directly solves the problem of defining a physical interacting ground state.

### Classification of the claims

Established from the stated baseline: The polynomial functional \\(\omega_P\\) is normalized and positive; a three-dimensional compressed dressed-annihilator pair has trivial common kernel for nonzero mixing; the free-case finite-CAR scalar-kernel comparison is established; and the general interacting comparison remains open.

Derived in this review: Spectral ground-state existence, canonical mixed ground-state construction, positive compression and transport identities, finite-dimensional no-go tests, and a nontrivial finite interacting example.

Conditional: Equality of physical and polynomial moments, ground-state transport, finite bosonic representation of an interacting Hamiltonian, and quantitative approximation estimates all require further hypotheses.

Contradicted: A general assertion that the finite interacting ground state is a simultaneous zero vector of the compressed dressed annihilators. Likewise, a global unital representation of the polynomial CCR algebra on a nonzero finite-dimensional CAR budget is impossible.

Unresolved: Whether the specific compressed Chapter 17 Hamiltonian, with its precise finite-band currents and couplings, has correlations equal or close to \\(\omega_P\\) for a useful nontrivial family of observables at \\(s\ne0\\).

The crucial distinction is between existence of a physical state and identification of that state with a particular oscillator functional.

## 2. Mathematical objects and assumptions

### 2.1 Physical fermionic carrier

Let \\(\mathcal H_F\\) be the finite occupation-CAR Hilbert space over the ordered multispecies momentum band

\\[ \Lambda^\*=\\{-h+1,\ldots,h\\},\qquad L=2h. \\]

For an admissible charge vector \\(\mathbf N\\) and a nonnegative excitation budget \\(K\\), define

\\[ B=B(\mathbf N,K) = \operatorname{span}\_{\mathbb C} \\{|S\rangle: \operatorname{charge}(S)=\mathbf N,\  e(S)\le K\\}. \\]

The inherited occupation inner product is positive definite.

Let

\\[ i:B\hookrightarrow\mathcal H_F \\]

be the canonical isometric inclusion. Its adjoint is the coordinate orthogonal projection onto \\(B\\), regarded as a map \\(\mathcal H_F\to B\\). Thus

\\[ i^\dagger i=I_B,\qquad P=ii^\dagger=P^\dagger=P^2. \\]

For \\(A\in\operatorname{End}(\mathcal H_F)\\), define

\\[ \operatorname{Comp}\_B(A)=i^\dagger A i. \\]

This is the compression map, not an algebra homomorphism.

For ambient operators \\(A,B\\),

\\[ \begin{aligned} \operatorname{Comp}\_B(AB) - \operatorname{Comp}\_B(A)\operatorname{Comp}\_B(B) &=i^\dagger ABi-i^\dagger Aii^\dagger Bi\\\ &=i^\dagger A(I-P)Bi. \end{aligned} \tag{2.1} \\]

This identity is exact, including operator order.

For typed source, intermediate and target spaces the corresponding identity is

\\[ P_tABP_s-P_tAP_mBP_s = P_tA(I-P_m)BP_s. \tag{2.2} \\]

Neither expression vanishes without an additional margin, invariance, or cancellation condition.

### 2.2 Physical interacting Hamiltonian

Let \\(H_F=H_F^\dagger\\) be a specified charge-preserving finite CAR Hamiltonian.

Its effective Hamiltonian on the chosen budget is

\\[ \boxed{H_B=i^\dagger H_Fi.} \tag{2.3} \\]

Then

\\[ H_B^\dagger=H_B. \\]

In particular, the existence theorem below does not require \\(B\\) to be invariant under \\(H_F\\).

However, this distinction matters physically:

\\[ H_B\ne H_F|\_B \\]

as operators on \\(B\\), unless \\(H_FB\subseteq B\\).

The compressed Hamiltonian is an exact definition of a finite effective problem; its eigenstates need not be eigenstates of the uncompressed Hamiltonian.

For the Chapter 17 model, the stipulated ambient operator is

\\[ H_F= \frac{2\pi}{L} \sum\_{m=1}^{M} \mathcal M_m(v_1,v_2) + H\_{\mathrm{zero}}, \tag{2.4} \\]

where

\\[ \begin{aligned} \mathcal M_m(v_1,v_2) ={}&v_1\big( \rho\_{R,m}\rho\_{R,-m} +\rho\_{L,m}\rho\_{L,-m} \big)\\\ &+v_2\big( \rho\_{R,m}\rho\_{L,m} +\rho\_{R,-m}\rho\_{L,-m} \big), \end{aligned} \tag{2.5} \\]

and

\\[ v_1=v_F+\frac{g_4}{2\pi}, \qquad v_2=\frac{g_2}{2\pi}. \\]

The source definitions specify the non-wrapping currents, and the interactions preserve the separate species charges.

Consequently, \\(H_B\\) is a genuine Hermitian finite matrix whenever the parameters are real and the corresponding current adjoint identities hold.

The condition

\\[ |v_2|\<v_1 \\]

is required for the stipulated stable hyperbolic Bogoliubov parametrization, not for finite-dimensional ground-state existence. A Hermitian finite matrix has a ground state even if the corresponding unbounded oscillator quadratic form would be unstable.

This is an important separation of the finite spectral theorem from the effective oscillator interpretation.

## 3. Construction, comparison maps, and no-go results

### 3.1 Option (a): The spectral interacting state

Let \\(B\ne\\{0\\}\\), \\(d=\dim\_{\mathbb C}B\\), and let \\(H_B=H_B^\dagger\\).

Write its distinct eigenvalues as

\\[ E_0\<E_1<\cdots\<E_r, \\]

with spectral projections \\(Q_j\\). If \\(H_B\\) is scalar, there is just \\(E_0\\).

By the finite-dimensional spectral theorem,

\\[ H_B=\sum\_{j=0}^r E_jQ_j,\qquad \sum\_{j=0}^rQ_j=I_B. \tag{3.1} \\]

Let \\(Q_0\\) project onto the lowest eigenspace and set

\\[ d_0=\operatorname{Tr}Q_0=\dim\ker(H_B-E_0I_B). \\]

Because \\(B\ne0\\), we have \\(d_0\ge1\\).

Define the canonical uniform ground-state density matrix

\\[ \boxed{\Gamma_0=\frac{Q_0}{d_0}.} \tag{3.2} \\]

Its associated functional is

\\[ \boxed{ \omega_B(O)=\operatorname{Tr}\_B(\Gamma_0O), \qquad O\in\operatorname{End}(B). } \tag{3.3} \\]

We obtain immediately

\\[ \Gamma_0^\dagger=\Gamma_0,\quad \Gamma_0\ge0,\quad \operatorname{Tr}\Gamma_0=1,\quad H_B\Gamma_0=E_0\Gamma_0. \\]

Furthermore,

\\[ \omega_B(I_B)=1 \\]

and

\\[ \omega_B(O^\dagger O) = \operatorname{Tr}(\Gamma_0O^\dagger O) = \frac1{d_0}\sum\_{a=1}^{d_0}\\|Oe_a\\|^2 \ge0, \tag{3.4} \\]

where \\(\\{e_a\\}\\) is an orthonormal basis of the ground eigenspace.

No annihilation equation enters this proof.

In fact, \\(Q_0\\) admits a finite polynomial characterization,

\\[ Q_0= \prod\_{j=1}^r \frac{H_B-E_jI_B}{E_0-E_j}, \tag{3.5} \\]

with the empty product interpreted as \\(I_B\\). This emphasizes that the construction is finite algebraic spectral theory, not an infinite-Hilbert-space construction.

Ground-state degeneracy requires particular care. If \\(d_0>1\\), there is no distinguished pure ground state. Every positive trace-one matrix \\(\Gamma\\) satisfying

\\[ Q_0\Gamma Q_0=\Gamma \tag{3.6} \\]

is a ground-state density matrix.

Conversely, a density matrix is supported on the ground eigenspace precisely when

\\[ \operatorname{Tr}(\Gamma H_B)=E_0. \tag{3.7} \\]

To prove the converse, observe that

\\[ \operatorname{Tr}\bigl(\Gamma(H_B-E_0I)\bigr) = \sum\_{j>0}(E_j-E_0)\operatorname{Tr}(\Gamma Q_j). \\]

Every summand is nonnegative. Their sum vanishes only when \\(\Gamma\\) has no support outside \\(Q_0B\\).

The uniform choice (3.2) is mathematically canonical and invariant under unitaries preserving the ground eigenspace. It is not the only zero-temperature ground state and does not resolve degeneracy through a physical selection principle.

For a chosen normalized eigenvector \\(\psi_0\in Q_0B\\), the pure state

\\[ \omega\_{\psi_0}(O)=\langle\psi_0,O\psi_0\rangle \\]

is equally legitimate.

### 3.2 Why dressed annihilation is a stronger and generally false requirement

Suppose the finite compressed dressed annihilators are \\(D\_{\nu m}\\).

To assert a dressed vacuum requires a normalized \\(\psi\in B\\) satisfying

\\[ D\_{\nu m}\psi=0 \qquad\text{for every retained mode.} \tag{3.8} \\]

This is independent of the spectral ground-state equation

\\[ H_B\psi=E_0\psi. \tag{3.9} \\]

Even an identity such as

\\[ H_B=E\_{\mathrm{shift}}I+ \sum\_{\nu,m}u_m D\_{\nu m}^\dagger D\_{\nu m}, \qquad u_m>0, \tag{3.10} \\]

would not establish (3.8) by itself. It would only show that a vector annihilated by all \\(D\_{\nu m}\\) saturates the lower bound \\(E\_{\mathrm{shift}}\\). Saturation must be proved separately.

In the finite setting, such a vector may not exist.

The source's three-dimensional counterexample makes the obstruction explicit. On

\\[ V=\operatorname{span}\\{1,X_R,X_L\\}, \\]

with normalized oscillator weight \\(m=1\\), define

\\[ D_R=cA_R^V+sC_L^V,\qquad D_L=cA_L^V+sC_R^V. \\]

In the orthonormal basis \\((1,X_R,X_L)\\),

\\[ D_R= \begin{pmatrix} 0&c&0\\\ 0&0&0\\\ s&0&0 \end{pmatrix}, \qquad D_L= \begin{pmatrix} 0&0&c\\\ s&0&0\\\ 0&0&0 \end{pmatrix}. \\]

Consequently,

\\[ D_R^\dagger D_R+D_L^\dagger D_L = \operatorname{diag}(2s^2,c^2,c^2). \tag{3.11} \\]

For \\(s\ne0\\), \\(c^2-s^2=1\\), this matrix is strictly positive. Hence

\\[ \ker D_R\cap\ker D_L=\\{0\\}. \tag{3.12} \\]

Nevertheless, the positive operator in (3.11) has a nonempty ground eigenspace.

For the monograph's \\(c=5/3,\ s=4/3\\), the matrix is

\\[ \operatorname{diag}(32/9,25/9,25/9), \\]

so its ground energy is \\(25/9\\), not zero. This example is also recorded in Appendix E.6.&#x20;

main.pdf



It disproves the universal inference from positive quadratic Hamiltonian to an annihilator vacuum. It does not disprove the existence of finite interacting spectral states.

### 3.3 Option (b): Transport by an isometry or positive map

Let \\(i:B\to\mathcal H\\) be an isometry between finite-dimensional complex Hilbert spaces.

Given a state \\(\omega_B\\), define

\\[ \boxed{ \omega\_{\mathcal H}(A)=\omega_B(i^\dagger Ai). } \tag{3.13} \\]

This is a legitimate state on \\(\operatorname{End}(\mathcal H)\\).

The underlying compression map

\\[ \Phi(A)=i^\dagger Ai \\]

is linear, unital, adjoint preserving and completely positive. Positivity follows, more concretely, from

\\[ \langle v,\Phi(A^\dagger A)v\rangle =\\|Aiv\\|^2\ge0. \\]

Normalization follows from

\\[ \Phi(I\_{\mathcal H})=i^\dagger i=I_B. \\]

In density-matrix form,

\\[ \Gamma\_{\mathcal H}=i\Gamma_Bi^\dagger, \qquad \operatorname{Tr}\_{\mathcal H}\Gamma\_{\mathcal H}=1, \tag{3.14} \\]

and

\\[ \operatorname{Tr}\_{\mathcal H}(\Gamma\_{\mathcal H}A) = \operatorname{Tr}\_B(\Gamma_Bi^\dagger Ai). \\]

For the actual inclusion \\(B\hookrightarrow\mathcal H_F\\), this gives a canonical extension of the budget ground state to the full occupation-CAR algebra.

It does not imply

\\[ \Phi(AB)=\Phi(A)\Phi(B). \\]

Equation (2.1) supplies the exact difference.

More generally, if \\(\mathcal A,\mathcal D\\) are finite-dimensional unital \\(\*\\)-algebras and

\\[ \Phi:\mathcal A\longrightarrow\mathcal D \\]

is unital and positive, then

\\[ \omega\_{\mathcal D}\circ\Phi \\]

is a state on \\(\mathcal A\\).

Complete positivity is a convenient stronger hypothesis, particularly if the comparison must remain positive after adjoining auxiliary systems. An arbitrary linear comparison map is insufficient.

There is also a Hamiltonian condition. Suppose \\(V:B\to W\\) is an isometry and

\\[ H_WV=VH_B. \tag{3.15} \\]

This intertwines the dynamics on the embedded subspace, but it does not guarantee that \\(V\psi_0\\) is a global ground state of \\(H_W\\): the orthogonal complement of \\(VB\\) could contain lower-energy vectors.

For ground-state transport, one must additionally require, for example,

\\[ H_W\ge E_0 I_W, \tag{3.16} \\]

and verify that the intended ground subspaces are related by \\(V\\). Equality of canonical uniform ground states also requires matching the full ground projections and degeneracies.

Why this does not automatically transfer \\(\omega_P\\) to CAR. The polynomial oscillator \\(\*\\)-algebra and the finite CAR endomorphism algebra have different carriers. The source's partition-state isometries connect protected finite vector spaces, not the entire polynomial algebra with the finite CAR algebra as multiplicative objects.

A map on observables must therefore be provided before one can write a meaningful pullback comparison.

There are trivial positive maps, such as

\\[ \Phi\_{\mathrm{triv}}(a)=\omega_P(a)I_B, \tag{3.17} \\]

for which

\\[ \omega_B(\Phi\_{\mathrm{triv}}(a))=\omega_P(a) \\]

holds for every polynomial oscillator observable \\(a\\). But \\(\Phi\_{\mathrm{triv}}\\) destroys the observable algebra: it is generally nonmultiplicative and does not identify oscillator generators with physical currents.

Thus equality through an arbitrary positive map is too weak to constitute bosonization. A meaningful map must preserve a specified physical dictionary.

### 3.4 Option (c): Finite moment comparisons

Let \\(w_1,\ldots,w_r\\) be chosen oscillator words, and let \\(O_1,\ldots,O_r\\) be explicitly corresponding finite-CAR observables, with each \\(O_j\\) acting on the correct carrier.

Define

\\[ \mu_j^P=\omega_P(w_j), \qquad \mu_j^F=\operatorname{Tr}(\Gamma_0O_j). \\]

The exact comparison discrepancies are

\\[ \boxed{ \delta_j=\mu_j^F-\mu_j^P. } \tag{3.18} \\]

This requires neither an oscillator density matrix on \\(B\\) nor a multiplicative map between algebras.

The polynomial moments satisfy finite positivity constraints. For any selected words \\(w_1,\ldots,w_r\\), the Gram matrix

\\[ G\_{ij}^P=\omega_P(w_i^\dagger w_j) \tag{3.19} \\]

is positive semidefinite, because

\\[ \sum\_{i,j}\overline{z_i}G\_{ij}^Pz_j = \omega_P\left[ \left(\sum_i z_iw_i\right)^\dagger \left(\sum_jz_jw_j\right) \right]\ge0. \tag{3.20} \\]

It therefore defines an exact finite-dimensional pre-Hilbert-space quotient of the span of the selected words by the null space of this Gram form.

No completion is needed.

But a positive matrix of abstract oscillator moments does not automatically define a state on the physically identified matrix observables.

For such an identification to be possible, the assignments

\\[ O_j\longmapsto\mu_j^P \\]

must respect every linear relation among the \\(O_j\\). They must also define a normalized positive functional on the self-adjoint unital operator space generated by the selected observables.

If these conditions hold, finite-dimensional positive extension theory allows a state on the whole matrix algebra. If they fail, no physical density matrix can reproduce those prescribed moments.

For example, if \\(Q_B\\) is a positive finite observable with

\\[ 0\le Q_B\le q\_{\max}I_B, \\]

then every density matrix satisfies

\\[ 0\le\operatorname{Tr}(\Gamma Q_B)\le q\_{\max}. \tag{3.21} \\]

Any proposed oscillator moment outside this interval fails the physical positivity constraints despite being perfectly valid as a moment of \\(\omega_P\\).

### 3.5 A general obstruction to matching every current moment

There is a stronger no-go theorem than the finite trace obstruction when one insists on the natural current-word dictionary.

Let \\(m>0\\) and suppose \\(A\_{\nu m}^F\\) is the genuine finite-band lowering current, which decreases the excitation energy by \\(m\\). Since \\(B(\mathbf N,K)\\) contains only nonnegative excitation energies at most \\(K\\),

\\[ (A\_{\nu m}^F)^q\psi=0 \qquad(\psi\in B) \\]

whenever

\\[ qm>K. \tag{3.22} \\]

This uses the physical energy grading, not a globally exact CCR.

Therefore, for any normalized physical state supported on \\(B\\),

\\[ \boxed{ \omega_B\bigl((C\_{\nu m}^F)^q(A\_{\nu m}^F)^q\bigr)=0 \quad(qm>K), } \tag{3.23} \\]

where the displayed product is evaluated using the ambient currents and the state extended to \\(\mathcal H_F\\).

By contrast, the algebraic squeezed state has

\\[ \boxed{ \omega_P(C\_{\nu m}^qA\_{\nu m}^q) =q!\\,(ms^2)^q. } \tag{3.24} \\]

This identity can be derived directly without assuming a completed general Wick theorem.

Using \\(\omega_P=\omega_0\circ\beta^{-1}\\),

\\[ \begin{aligned} \omega_P(C_R^qA_R^q) = \omega_0\big[ (cC_R-sA_L)^q (cA_R-sC_L)^q \big]. \end{aligned} \\]

Since different branches commute, every term vanishes in the vacuum expectation except the term containing \\(A_L^qC_L^q\\). Its coefficient is \\(s^{2q}\\), and

\\[ \omega_0(A_L^qC_L^q)=q!m^q. \\]

This proves (3.24).

If \\(s\ne0\\), the expression is strictly positive. Combining (3.23) and (3.24),

\\[ \boxed{ \omega_B((C\_{\nu m}^F)^q(A\_{\nu m}^F)^q) \ne \omega_P(C\_{\nu m}^qA\_{\nu m}^q) \quad\text{for }qm>K. } \tag{3.25} \\]

This excludes equality of all naturally corresponding current-word moments at any fixed finite budget when \\(s\ne0\\).

It is not merely a failure of one particular trial ground state: no density matrix supported on the budget can repair it.

Even at \\(s=0\\), equality of all ordered moments is impossible if one demands a multiplicative finite CCR representation. The reverse-ordered vacuum moment

\\[ \omega_0(A^qC^q)=q!m^q \\]

cannot be reproduced after enough raising operations exceed the budget.

These are exact finite obstructions. They do not exclude selected low-order moment agreement under suitable margins, nor nonmultiplicative positive comparison maps.

## 4. Exact finite interacting example: the Chapter 17 pairing Hamiltonian

The source already contains parameters suitable for a substantially stronger non-vacuity test than a generic two-level matrix.

Use the Chapter 18 example:

\\[ \begin{gathered} h=8,\quad L=16,\quad M=2,\quad K=2,\\\ N_R=N_L=0,\\\ v_F=1,\quad g_4=32\pi,\quad g_2=30\pi. \end{gathered} \\]

Thus

\\[ v_1=17,\qquad v_2=15, \\]

and the stable oscillator parameters are

\\[ u=8,\qquad c=\frac54,\qquad s=\frac34. \tag{4.1} \\]

These parameters and their current-margin hypotheses occur in the source's worked example.&#x20;

main.pdf



The margins include

\\[ 2M+K=6\le h=8,\qquad 2K+|N\_\nu|=4\le8. \\]

Therefore, the actual partition-state basis and the relevant low-energy current actions are available.

### 4.1 The eight-dimensional physical budget

Write \\(\Omega\\) for the normalized zero-charge fermionic sea, and identify the protected current actions with \\(C\_{\nu m}\\) and \\(A\_{\nu m}\\).

The total excitation-budget space \\(B(\mathbf0,2)\\) has the following eight orthonormal partition states:

| State                                                      | Excitation energy |
| ---------------------------------------------------------- | ----------------- |
| \\(\Omega\\)                                               | 0                 |
| \\(C\_{R1}\Omega\\), \\(C\_{L1}\Omega\\)                   | 1                 |
| \\(C\_{R1}C\_{L1}\Omega\\)                                 | 2                 |
| \\(C\_{R1}^2\Omega/\sqrt2\\), \\(C\_{L1}^2\Omega/\sqrt2\\) | 2                 |
| \\(C\_{R2}\Omega/\sqrt2\\), \\(C\_{L2}\Omega/\sqrt2\\)     | 2                 |

The normalizations follow from the actual partition Gram factors \\(z_p=\prod_m m^{k_m}k_m!\\).

Set

\\[ \alpha=\frac{2\pi}{L}=\frac{\pi}{8} \\]

and compress the specified current Hamiltonian,

\\[ H_B= P_B\left[ \alpha\sum\_{m=1}^{2} \left( v_1(C\_{Rm}A\_{Rm}+C\_{Lm}A\_{Lm}) +v_2(C\_{Rm}C\_{Lm}+A\_{Rm}A\_{Lm}) \right) \right]P_B, \tag{4.2} \\]

restricted to \\(B\\). The zero-mode term is zero in this charge sector.

The key observation is that the pair-creation term for \\(m=2\\) raises the excitation energy by four, and therefore its action on \\(\Omega\\) is discarded by the final projection.

For \\(m=1\\), pair creation reaches energy two and survives.

Define

\\[ |11\rangle=C\_{R1}C\_{L1}\Omega. \\]

The subspace

\\[ W=\operatorname{span}\\{\Omega,|11\rangle\\} \\]

is invariant under \\(H_B\\), and

\\[ \boxed{ H_B|\_W= \alpha \begin{pmatrix} 0&v_2\\\ v_2&2v_1 \end{pmatrix}. } \tag{4.3} \\]

The remaining six basis vectors are eigenvectors. The two single-excitation states have eigenvalue \\(\alpha v_1\\), while the four remaining energy-two states have eigenvalue \\(2\alpha v_1\\).

Consequently, this is an exact block decomposition of the compressed finite Hamiltonian, not an uncontrolled two-level approximation.

### 4.2 Exact spectrum and normalized ground state

The two eigenvalues of (4.3) are

\\[ E\_\pm=\alpha\left(v_1\pm\sqrt{v_1^2+v_2^2}\right). \tag{4.4} \\]

For \\(v_1>0\\) and \\(v_2\ne0\\),

\\[ E\_-<0<\alpha v_1, \\]

so the ground state is unique.

Introduce

\\[ D=\sqrt{v_1^2+v_2^2},\qquad \eta=\frac{v_2}{v_1+D}. \\]

Then an exactly normalized interacting ground ket is

\\[ \boxed{ |\psi\_{\mathrm{gs}}\rangle = \frac{|\Omega\rangle-\eta|11\rangle} {\sqrt{1+\eta^2}}. } \tag{4.5} \\]

For the numerical source parameters,

\\[ D=\sqrt{514},\qquad \eta=\frac{15}{17+\sqrt{514}}. \\]

Its ground energy is

\\[ \boxed{ E\_{\mathrm{gs}} = \frac{\pi}{8}(17-\sqrt{514})<0. } \tag{4.6} \\]

The physical interacting state is

\\[ \Gamma\_{\mathrm{gs}} = |\psi\_{\mathrm{gs}}\rangle \langle\psi\_{\mathrm{gs}}|. \tag{4.7} \\]

This supplies an exact, nontrivial interacting spectral state on a genuine finite fermionic budget.

The construction follows mathematically from the supplied current and partition identities. It is not claimed to be a previously established Lean theorem.

### 4.3 Direct comparison of interacting correlations

The number-like bare current observable gives

\\[ \begin{aligned} \langle C\_{R1}A\_{R1}\rangle\_{\mathrm{gs}} &=\frac{\eta^2}{1+\eta^2}\\\ &=\frac12\left(1-\frac{v_1}{\sqrt{v_1^2+v_2^2}}\right). \end{aligned} \tag{4.8} \\]

Similarly,

\\[ \langle C\_{R1}C\_{L1}\rangle\_{\mathrm{gs}} = -\frac{\eta}{1+\eta^2} = -\frac{v_2}{2\sqrt{v_1^2+v_2^2}}. \tag{4.9} \\]

On the polynomial oscillator side,

\\[ \omega_P(C\_{R1}A\_{R1})=s^2, \qquad \omega_P(C\_{R1}C\_{L1})=-cs. \tag{4.10} \\]

For the same parameters, the results are:

| Ordered observable   | Finite interacting ground state                    | Polynomial \\(\omega_P\\) |
| -------------------- | -------------------------------------------------- | ------------------------- |
| \\(C\_{R1}A\_{R1}\\) | \\(\frac12(1-\frac{17}{\sqrt{514}})\approx0.125\\) | \\(9/16=0.5625\\)         |
| \\(C\_{R1}C\_{L1}\\) | \\(-\frac{15}{2\sqrt{514}}\approx-0.331\\)         | \\(-15/16=-0.9375\\)      |

These are exact inequalities, not numerical evidence or floating-point discrepancies.

They show that, for this compressed Hamiltonian and the natural current dictionary,

\\[ \boxed{ \omega\_{\mathrm{gs}}\ne\omega_P \quad\text{even on the selected quadratic current moments.} } \tag{4.11} \\]

Importantly, this compares an actual interacting finite ground state with the interacting polynomial state. It is stronger than comparing the bare sea with \\(\omega_P\\).

The example also makes the finite squeezed-vacuum obstruction tangible. The projected dressed right annihilator acts on (4.5) as

\\[ D_R|\psi\_{\mathrm{gs}}\rangle = \frac{s-c\eta}{\sqrt{1+\eta^2}}\\, C\_{L1}\Omega. \tag{4.12} \\]

Here

\\[ \frac{s}{c}=\frac35 \ne \frac{15}{17+\sqrt{514}}=\eta. \\]

Thus \\(D_R\psi\_{\mathrm{gs}}\ne0\\).

The physical ground state exists and is unique, yet fails the dressed annihilation equation.

### 4.4 Why the mismatch occurs

The oscillator Bogoliubov transformation diagonalizes a quadratic form using the global CCR. In the polynomial carrier, occupation is unbounded.

The finite budget instead removes excitation channels. In particular,

\\[ P_B C\_{R2}C\_{L2}P_B=0 \\]

on the chosen source budget, even though the corresponding polynomial oscillator pairing operator is nonzero.

The compressed Hamiltonian therefore has a different spectral problem from the uncompressed oscillator Hamiltonian.

This observation is stronger than saying that a formal squeezed vector is difficult to normalize: it explains why the physical finite ground-state coefficients differ from the infinite-oscillator Bogoliubov coefficients.

At \\(v_2=0\\), the exact ground state becomes \\(\Omega\\), while \\(s=0\\). The protected quadratic contractions then agree with \\(\omega_0\\), consistently with Chapter 19.

In the pinned source, the corresponding free scalar-kernel result is `fock_ground_matches_free_state` in `Bosonize/Core/Ch19Correlations.lean`. The manuscript's Chapter 19, Section 19.5 describes the same restricted free comparison.&#x20;

main.pdf



The \\(s=0\\) result is therefore a valid special case. It supplies neither an interacting-state continuation theorem nor a guarantee of finite-\\(s\\) equality.

## 5. Dependencies and minimal version 1 theorems

The mathematical dependencies are:

Actual finite CAR Fock space

Occupation basis, inner product, adjoints, charge and excitation-energy grading

Nonzero budget \\(B(\mathbf N,K)\\) and orthogonal projection

Specified Hermitian \\(H_B=P_BH_FP_B|\_B\\)

Spectral ground projection \\(Q_0\\) and density matrix \\(\Gamma_0\\)

Finite CAR correlations

\\(\operatorname{Tr}(\Gamma_0O_j)\\)

Oscillator comparison

\\(\omega_P(w_j)\\), observable dictionary required

Exact moment identities, counterexamples, or error bounds

The minimal mathematical theorem package I recommend for version 1 is the following.

Theorem 1 — Finite spectral ground-state existence. Given a nonzero finite budget and a specified Hermitian compressed Hamiltonian, there exists a positive trace-one ground-state density matrix. The normalized ground spectral projection provides a canonical choice.

Theorem 2 — Characterization of all ground states. A density matrix is a ground-state density matrix if and only if its support lies in the lowest eigenspace, equivalently if its expected energy equals the lowest eigenvalue.

Theorem 3 — Positive state extension. An isometric inclusion induces a positive unital compression on ambient observables and extends every finite-budget state to a positive normalized state on the ambient finite CAR algebra. The failure of multiplicativity is given exactly by (2.1).

Theorem 4 — Conditional comparison of moments. Given explicit lists of corresponding physical operators and oscillator words, their moment discrepancies are well-defined. Zero discrepancy is an additional equality hypothesis or a separate theorem, not a consequence of state existence.

Theorem 5 — Finite-budget all-moment obstruction. For a positive lowering mode and nonzero \\(s\\), the finite energy budget and the polynomial oscillator state disagree on sufficiently high moments of the form \\(C^qA^q\\).

Theorem 6 — Nontrivial finite interacting witness. In the \\(L=16\\), \\(M=K=2\\) example, the compressed pairing Hamiltonian has the exact spectral block (4.3), a unique interacting ground state, and the nonzero current-moment discrepancies (4.8)–(4.11).

These statements provide a closed, independently testable mathematical answer to the state-carrier question.

The first three establish the state carrier without any oscillator comparison. The next two make the comparison logically precise. The sixth prevents the theory from stopping at a vacuous existence result.

### A quantitative alternative to exact equality

Suppose \\(H_B\\) has a unique ground state \\(\psi_0\\), energy \\(E_0\\), and spectral gap

\\[ \Delta=E_1-E_0>0. \\]

Let \\(\phi\in B\\) be any normalized trial state, possibly obtained by transporting a finite polynomial truncation through the partition-state isometry.

Define its energy excess

\\[ \varepsilon = \langle\phi,H_B\phi\rangle-E_0\ge0. \\]

Expanding in the eigenbasis gives

\\[ \varepsilon \ge \Delta\left(1-|\langle\psi_0,\phi\rangle|^2\right). \tag{5.1} \\]

The trace distance of two pure states therefore obeys

\\[ \bigl\\| |\psi_0\rangle\langle\psi_0| - |\phi\rangle\langle\phi| \bigr\\|\_1 \le 2\sqrt{\varepsilon/\Delta}. \tag{5.2} \\]

For any finite observable \\(O_B\\),

\\[ \left| \langle\psi_0,O_B\psi_0\rangle - \langle\phi,O_B\phi\rangle \right| \le 2\\|O_B\\|\sqrt{\varepsilon/\Delta}. \tag{5.3} \\]

Now let \\(w\\) be its specified oscillator counterpart. The triangle inequality yields

\\[ \boxed{ \begin{aligned} &\left|\omega\_{\mathrm{gs}}(O_B)-\omega_P(w)\right|\\\ &\quad\le 2\\|O_B\\|\sqrt{\varepsilon/\Delta} + \left|\langle\phi,O_B\phi\rangle-\omega_P(w)\right|. \end{aligned} } \tag{5.4} \\]

This separates two different sources of error:

1. Spectral approximation error: How close is a trial finite vector to the actual finite interacting ground state?
2. Bosonization comparison error: How closely do that trial vector's moments agree with the formal oscillator moments?

The second contribution cannot simply be discarded. It includes finite-budget boundary effects, truncated oscillator occupations, and any additional mismatch in the proposed observable dictionary.

For degenerate ground spaces, the same energy argument controls the weight outside the ground projection, but does not select a particular state within the degenerate eigenspace. A separate selection criterion is necessary.

Equation (5.4) is a rigorous candidate for a future comparison theorem. It requires no thermodynamic limit or Gaussian-state identification.

## 6. Remaining questions, source status, and literature

### Questions that genuinely remain

The spectral existence question is resolved by finite-dimensional mathematics. The remaining choices concern what comparison is intended.

1\. Which finite Hamiltonian is the primary interacting model? The Chapter 17 `luttingerBosonizedHamiltonian`, the raw microscopic four-fermion interaction, and the alternative hopping model are not automatically equivalent. This matters because the actual physical ground state depends on the operator chosen.

2\. Which observable dictionary is intended? For a given oscillator word, does the physical target mean the ambient ordered current word subsequently compressed, or the product of individually compressed currents? These choices can differ by the exact discarded-channel term.

3\. Which states should be compared in degenerate sectors? A selected pure ground state, the normalized ground spectral projection, or a symmetry-selected mixture? The latter two may have different correlation functions.

4\. What is the intended finite comparison family? Selected quadratic current kernels provide the least assumption-heavy target. Charge-changing fields and CDW/SC products require additional typed source, target, and intermediate budget conditions.

5\. Which approximation parameter is to be controlled? At fixed \\(h,M,K\\), the discrepancy is an exact finite number. A small-coupling expansion or a sequence of larger protected budgets would constitute a separate quantitative problem and must specify the quantities held fixed.

A further technical distinction concerns \\(H_F\\) versus \\(H_B\\): when \\(B\\) is not invariant, should the physical goal be the compressed effective problem itself, or approximation of an eigenstate of the full finite-band Hamiltonian? These are different spectral questions.

### Literature verification

The following references were checked against publisher or institutional bibliographic records.

Daniel C. Mattis and Elliott H. Lieb (1965). “Exact Solution of a Many-Fermion System and Its Associated Boson Field.” Journal of Mathematical Physics 6(2), 304–312. DOI: [10.1063/1.1704281](https://doi.org/10.1063/1.1704281?utm_source=chatgpt.com).&#x20;

[image](https://www.google.com/s2/favicons?domain=https://collaborate.princeton.edu\&sz=32)

Princeton University



This is the central historical reference for the density-commutator and finite-versus-Dirac-sea distinction. Its infinite-sea treatment must not be silently promoted to a global finite-band CCR representation.

Thierry Giamarchi (2003). Quantum Physics in One Dimension. Oxford University Press. DOI: [10.1093/acprof:oso/9780198525004.001.0001](https://doi.org/10.1093/acprof:oso/9780198525004.001.0001?utm_source=chatgpt.com).&#x20;

[image](https://www.google.com/s2/favicons?domain=https://academic.oup.com\&sz=32)

Oxford Academic



This supplies the standard interacting Luttinger-liquid and bosonization setting, but does not establish the specific finite-budget state comparison requested here.

Huzihiro Araki (1970/1971). “On Quasifree States of CAR and Bogoliubov Automorphisms.” Publications of the Research Institute for Mathematical Sciences 6(3), 385–442. DOI: [10.2977/prims/1195193913](https://doi.org/10.2977/prims/1195193913?utm_source=chatgpt.com).&#x20;

[image](https://www.google.com/s2/favicons?domain=https://ems.press\&sz=32)

EMS Press

+1



The publication-year distinction reflects differences in the available journal records. This reference provides rigorous CAR quasifree-state theory; such states are not automatically the CCR oscillator functional \\(\omega_P\\).

### Repository and manuscript status

I checked the provided monograph and the pinned GitHub source files relevant to this question, including:

- `A07InteractionsAndBogoliubov.lean`
- `Ch17LuttingerModels.lean`
- `Ch18Bogoliubov.lean`
- `A08OscillatorStates.lean`
- `Ch19Correlations.lean`

The pinned source includes the polynomial-state and free comparison results. In particular, it contains `omegaP_one`, the positive Gram-form result `omegaP_gramSum`, the dressed vacuum-order identities, and `fock_ground_matches_free_state`.

The source also contains the compressed three-dimensional counterexample.

I have not run Lean, established any new Core promotion, or checked the proposed spectral theorems in Lean. The exact eight-dimensional interacting calculation in Section 4 is a mathematical derivation from the supplied finite conventions and requires independent formal verification before it may be described as a repository theorem.

## Final recommendation

For version 1, the appropriate minimal result is a finite interacting ground-state theorem together with an explicitly bounded comparison problem, not an identification of that state with the unrestricted oscillator vacuum.

The physical state should be defined spectrally from the actual Hermitian compressed CAR Hamiltonian. The polynomial \\(\omega_P\\) should remain a separate positive algebraic state supplying exact reference moments.

The \\(L=16\\), \\(K=M=2\\) example is especially useful because it demonstrates all the relevant distinctions within the project's own finite conventions: a nonzero physical budget, a genuine interacting Hamiltonian, a unique normalized ground ket, valid current margins, and an exact failure of the proposed Gaussian moment identification.

The state-existence obstruction is resolved. The natural all-moment identification is false at finite budget for nonzero mixing. The remaining scientifically meaningful target is a specified family of physical observables with exact finite discrepancies or justified quantitative error bounds.
