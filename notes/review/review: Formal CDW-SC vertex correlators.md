# Independent mathematical review: Formal CDW/SC vertex correlators

Project: [Bosonize-Lean](https://github.com/lufreitas0000/bosonize-lean?utm_source=chatgpt.com) Baseline: `40dea8bfbdc849417c072e490480d4f72536116a` Scope: Chapter 20.2 / CH20b, finite formal oscillator–charge construction

## 1. Verdict

The proposed CDW and SC correlator identities are mathematically correct under the stated algebraic hypotheses. They can be derived coefficientwise from the uncompressed CCR, the Bogoliubov-pulled-back state, and the ordered charge shifts. No correction to their exponents, charge phases, or \\(L^{-2}\\) normalization is necessary.

For \\(J\in\\{D,S\\}\\), define

\\[ \begin{aligned} g_D&=(c-s)^2=g,\\\ g_S&=(c+s)^2=g^{-1},\\\ a_D(N)&=N_L-N_R-1,\\\ a_S(N)&=N_R+N_L. \end{aligned} \\]

The result is

\\[ \boxed{ \begin{aligned} &\widehat\omega\_{P,N} \left(W_J(t,x)^\dagger W_J(t,y)\right)\\\ &\qquad= \frac{\zeta^{a_J(N)(y-x)}}{L^2} \operatorname{Exp}\_{\mathrm f} \left[-2g_JD_1(x,y)t^2\right]. \end{aligned} } \tag{1} \\]

This is an equality in \\(\mathbb C[[t]]\\), not an identity obtained by evaluating an analytic exponential at \\(t=1\\).

### Classification of conclusions

| Statement                                                        | Verdict                                                                          |
| ---------------------------------------------------------------- | -------------------------------------------------------------------------------- |
| Hermiticity of \\(X_D(x)\\), \\(X_S(x)\\)                        | Derived and valid                                                                |
| Same-channel commutation at different positions                  | Derived and valid                                                                |
| Absence of a same-channel BCH correction                         | Valid                                                                            |
| Ordered charge phases \\(a_D,a_S\\)                              | Valid for the specified \\(F_R,F_L\\)                                            |
| Gaussian moment formula                                          | Derivable directly from the polynomial CCR vacuum                                |
| Equation (1), including all coefficients                         | Derived and valid                                                                |
| Normal-ordered correlator has the same expression                | False without a compensating normalization                                       |
| Formal vertices equal finite-CAR CDW/SC observables              | Not established; the stated normalization fails a concrete free-state comparison |
| Interacting finite-CAR ground state realizes \\(\omega\_{P,N}\\) | Unresolved                                                                       |
| Equality after finite-energy compression                         | Not implied and generally obstructed                                             |

The supplied monograph already gives the proposed calculation in Chapter 20.2, particularly Lemma 20.18, Proposition 20.20, Lemmas 20.21–20.23, and draft Theorem 20.25. Appendix E summarizes the formal construction and its limitations.&#x20;

main.pdf



I verified that the specified GitHub commit exists and inspected the corresponding Chapter 20 manuscript and selected Lean sources. The finite `Ch20CDW.lean` and algebraic `A08OscillatorStates.lean` modules are distinct from the remaining formal-vertex construction. Nothing in this review constitutes a Lean verification of Equation (1).

The particularly important distinction is that a theorem about formal vertices is not a theorem about bosonization of the actual finite fermion operators. The first is justified by the mathematics below; the second requires additional operator and state comparison results.

## 2. Mathematical objects and assumptions

Let \\(h,M\in\mathbb N\_{>0}\\), \\(L=2h\\), and \\(\Lambda=\mathbb Z/L\mathbb Z\\). The finite Fourier characters are

\\[ \zeta^{mx}=\exp(2\pi i mx/L), \qquad x\in\Lambda,\quad m\in\mathbb Z. \\]

All oscillator indices belong to

\\[ \mathcal I_M=\\{R,L\\}\times\\{1,\ldots,M\\}. \\]

There is no need for \\(M\leq h\\) in the abstract formal identity. Such a restriction becomes relevant only when comparing these oscillators with the physical finite momentum band.

### 2.1 The joint carrier

Use the algebraic spaces

\\[ \mathcal H\_{\mathrm{ch}}^{\mathrm{alg}} =\mathbb C^{(\mathbb Z^2)}, \qquad \mathcal P_M =\mathbb C[X\_{\nu m}:(\nu,m)\in\mathcal I_M]. \\]

The joint representation carrier is

\\[ \mathcal D =\mathcal H\_{\mathrm{ch}}^{\mathrm{alg}} \otimes\_{\mathbb C}\mathcal P_M. \\]

Both factors have positive-definite algebraic inner products. The charge basis is orthonormal and the oscillator monomials have the pairing specified in the question.

The CCR are

\\[ [A\_{\nu m},C\_{\eta n}] =m\delta\_{\nu\eta}\delta\_{mn}I, \\]

with all creator–creator and annihilator–annihilator commutators zero.

The Bogoliubov transformation is a star-algebra automorphism because \\(c,s\\) are real and \\(c^2-s^2=1\\). Set

\\[ \widetilde C\_{\nu m}=\beta(C\_{\nu m}), \qquad \widetilde A\_{\nu m}=\beta(A\_{\nu m}). \\]

Then

\\[ \widetilde C\_{\nu m}^{\dagger} =\widetilde A\_{\nu m}. \\]

The state \\(\omega_P=\omega_0\circ\beta^{-1}\\) has contractions

\\[ \begin{aligned} \omega_P(\widetilde A\_{\nu m}\widetilde C\_{\eta n}) &=m\delta\_{\nu\eta}\delta\_{mn},\\\ \omega_P(\widetilde C\_{\nu m}\widetilde A\_{\eta n}) &=0,\\\ \omega_P(\widetilde A\widetilde A) &=\omega_P(\widetilde C\widetilde C)=0. \end{aligned} \tag{2} \\]

The tensor-product charge/oscillator functional is defined on the algebraic operator words, and its coefficientwise extension acts on formal power series.

Crucially, \\(\widehat\omega\_{P,N}\\) is not a multiplicative functional:

\\[ \widehat\omega\_{P,N}(AB) \ne \widehat\omega\_{P,N}(A) \widehat\omega\_{P,N}(B) \\]

in general. Only charge/oscillator tensor-factor independence provides the factorization needed below.

### 2.2 Ordered charge words

Let \\(Z_J(x)\\) denote the diagonal operator

\\[ Z_J(x)|N\rangle =\zeta^{a_J(N)x}|N\rangle. \\]

Write

\\[ K_D(x)=F_R^\dagger F_L Z_D(x), \qquad K_S(x)=F_R F_L Z_S(x). \\]

The factor \\(Z_J(x)\\) acts first. This fixes the ordering ambiguity completely.

The vertex lives in a formal-series algebra:

\\[ W_J(t,x) =\frac1L K_J(x)\operatorname{Exp}\_{\mathrm f}(itX_J(x)) \in\mathfrak A[[t]]. \\]

The involution is antilinear, reverses operator products, and fixes \\(t\\).

## 3. Derivation and independent checks

### 3.1 Exact charge-shift calculation

For the specified simplified Klein convention,

\\[ F_R|N_R,N_L\rangle =|N_R-1,N_L\rangle, \\]

\\[ F_L|N_R,N_L\rangle =(-1)^{N_R}|N_R,N_L-1\rangle. \\]

Consequently,

\\[ F_R^\dagger F_L|N\rangle =(-1)^{N_R}|N+e_R-e_L\rangle, \\]

and

\\[ F_RF_L|N\rangle =(-1)^{N_R}|N-e_R-e_L\rangle. \\]

The charge shifts are therefore

\\[ \delta_D=e_R-e_L, \qquad \delta_S=-e_R-e_L. \\]

Including the source phase gives

\\[ \boxed{ K_D(x)|N\rangle =(-1)^{N_R} \zeta^{(N_L-N_R-1)x} |N+\delta_D\rangle } \tag{3} \\]

and

\\[ \boxed{ K_S(x)|N\rangle =(-1)^{N_R} \zeta^{(N_R+N_L)x} |N+\delta_S\rangle. } \tag{4} \\]

The adjoint \\(K_J(x)^\dagger\\) returns the shifted ket to its original charge and conjugates the coefficient from the original source charge.

Hence

\\[ \begin{aligned} K_J(x)^\dagger K_J(y)|N\rangle &= (-1)^{2N_R} \zeta^{-a_J(N)x} \zeta^{a_J(N)y}|N\rangle\\\ &=\zeta^{a_J(N)(y-x)}|N\rangle. \end{aligned} \\]

Thus, as an operator identity on the charge basis,

\\[ \boxed{ K_J(x)^\dagger K_J(y) =\zeta^{a_J(\widehat N)(y-x)}. } \tag{5} \\]

In particular,

\\[ K_J(x)^\dagger K_J(x)=I. \\]

The charge normalization contributes exactly one, with no extra factor or surviving Klein sign.

An ordering counterexample. If the diagonal phase were moved to the left of either complete charge-shift word without changing its definition, the phase would act on the target rather than the source. In both channels,

\\[ a_J(N+\delta_J)=a_J(N)-2. \\]

That alternative order would change the vertex by \\(\zeta^{-2x}\\). This difference is nontrivial on a general even lattice and cannot be silently absorbed into the original definition.

#### Comparison with the manuscript Klein convention

The actual Chapter 20.2 manuscript uses the more elaborate finite-sea signs

\\[ P_R(N)=(-1)^{h+N_R-1}, \qquad P_L(N)=(-1)^{N_R+N_L-1}. \\]

These are not literally the simplified conventions in the question. However, they are related by a diagonal charge-basis rephasing

\\[ U_h|N\rangle=\eta_h(N)|N\rangle, \\]

where

\\[ \eta_h(N)= (-1)^{hN_R+\frac{N_R(N_R-1)}2+ \frac{N_L(N_L-1)}2}. \\]

Direct substitution shows that conjugating the manuscript shifts by \\(U_h\\) gives the simplified shifts \\(F_R|N\rangle=|N-e_R\rangle\\) and \\(F_L|N\rangle=(-1)^{N_R}|N-e_L\rangle\\).

Because \\(U_h\\) is diagonal, it commutes with every \\(Z_J(x)\\). Thus this change of charge-basis gauge does not alter Equation (5) or the charge-diagonal two-point correlator. It would nevertheless matter when comparing individual charged matrix elements or vertex operators across different conventions.

### 3.2 Hermiticity and exact commutators

Define

\\[ S_M(d)=\sum\_{m=1}^M \frac{\sin(2\pi md/L)}m. \\]

The opposite chiral orientations imply

\\[ [Q\_\nu(x),Q\_\nu(y)] =2i\epsilon\_\nu S_M(x-y)I. \tag{6} \\]

Since the dressed right and left oscillator families commute,

\\[ [Q_R(x),Q_L(y)]=0. \\]

Therefore

\\[ \begin{aligned} [Q_R(x)+Q_L(x),Q_R(y)+Q_L(y)]&=0,\\\ [Q_R(x)-Q_L(x),Q_R(y)-Q_L(y)]&=0. \end{aligned} \\]

Multiplying by the real Bogoliubov coefficients establishes

\\[ \boxed{ [X_J(x),X_J(y)]=0,\qquad J=D,S. } \tag{7} \\]

Hermiticity follows independently from

\\[ \overline{\zeta^{mx}}=\zeta^{-mx}, \qquad \widetilde C\_{\nu m}^\dagger =\widetilde A\_{\nu m}, \\]

so \\(X_J(x)^\dagger=X_J(x)\\).

The commutator cancellation is specific to equal channels. For example,

\\[ \boxed{ [X_D(x),X_S(y)] =4iS_M(x-y)I, } \tag{8} \\]

because \\((c-s)(c+s)=1\\). This generally does not vanish.

Thus the same-channel correlator needs no BCH correction, whereas products of different vertex types can acquire a nontrivial central BCH factor before their charge-sector matrix elements are considered.

### 3.3 Exact oscillator variance

For each channel define

\\[ Y_J(x,y)=X_J(y)-X_J(x). \\]

Introduce

\\[ \lambda_D=c-s,\qquad\lambda_S=c+s, \\]

and branch signs

\\[ (\eta_R^D,\eta_L^D)=(1,1), \qquad (\eta_R^S,\eta_L^S)=(1,-1). \\]

Then \\(Y_J\\) has the Hermitian decomposition

\\[ Y_J =\sum\_{\nu,m} \left( f\_{\nu m}\widetilde C\_{\nu m} +\overline{f\_{\nu m}}\widetilde A\_{\nu m} \right), \\]

where

\\[ f\_{\nu m} = \frac{\lambda_J\eta\_\nu^J}{m} \left( \zeta^{-\epsilon\_\nu my} -\zeta^{-\epsilon\_\nu mx} \right). \tag{9} \\]

From the ordered contractions (2),

\\[ \omega_P(Y_J)=0, \\]

and

\\[ \omega_P(Y_J^2) =\sum\_{\nu,m}m|f\_{\nu m}|^2. \\]

Now use

\\[ |\zeta^{-\epsilon\_\nu my} -\zeta^{-\epsilon\_\nu mx}|^2 = 2\left[1-\cos\left(\frac{2\pi m(x-y)}L\right)\right]. \\]

Both chiralities contribute equally, independently of the signs \\(\eta\_\nu^J\\). It follows that

\\[ \begin{aligned} \omega_P(Y_J^2) &=2\lambda_J^2 \sum\_{\nu=R,L}\sum\_{m=1}^M \frac{1-\cos(2\pi m(x-y)/L)}m\\\ &=4g_JD_1(x,y). \end{aligned} \\]

Therefore

\\[ \boxed{ V_J(x,y):=\omega_P(Y_J^2) =4g_JD_1(x,y). } \tag{10} \\]

This factor of four is essential. Each chirality contributes \\(2g_JD_1\\); the full variance contains two chiralities.

### 3.4 Derivation of the Wick identity

It is unnecessary to assume a Gaussian probability measure or invoke a completed Weyl algebra.

Consider an arbitrary Hermitian linear combination of dressed modes,

\\[ Y=C_f+A\_{\overline f}, \\]

with

\\[ C_f=\sum_j f_j\widetilde C_j, \qquad A\_{\overline f} =\sum_j\overline{f_j}\widetilde A_j. \\]

The coefficients must be complex conjugates. This is important for both Hermiticity and the nonnegative variance.

Set

\\[ V=\sum_jm_j|f_j|^2. \\]

Then the CCR give

\\[ [A\_{\overline f},Y]=VI. \\]

The commutator is central, and consequently

\\[ [A\_{\overline f},Y^n]=nVY^{n-1}. \tag{11} \\]

Using the ordered dressed-vacuum equations

\\[ \omega_P(aA\_{\overline f})=0, \qquad \omega_P(C_fa)=0, \\]

we obtain, for \\(n\ge1\\),

\\[ \begin{aligned} \omega_P(Y^{n+1}) &=\omega_P((C_f+A\_{\overline f})Y^n)\\\ &=\omega_P(A\_{\overline f}Y^n)\\\ &=\omega_P([A\_{\overline f},Y^n])\\\ &=nV\omega_P(Y^{n-1}). \end{aligned} \tag{12} \\]

The initial conditions are

\\[ \omega_P(I)=1,\qquad \omega_P(Y)=0. \\]

Thus the moments are

\\[ \boxed{ \begin{aligned} \omega_P(Y^{2k+1})&=0,\\\ \omega_P(Y^{2k}) &=(2k-1)!!\\,V^k =\frac{(2k)!}{2^kk!}V^k. \end{aligned} } \tag{13} \\]

Expanding the formal exponential coefficientwise,

\\[ \begin{aligned} \widehat\omega_P \left(\operatorname{Exp}\_{\mathrm f}(itY)\right) &=\sum\_{k=0}^\infty \frac{i^{2k}t^{2k}}{(2k)!} \frac{(2k)!}{2^kk!}V^k\\\ &=\sum\_{k=0}^\infty \frac{(-V/2)^k}{k!}t^{2k}. \end{aligned} \\]

Therefore

\\[ \boxed{ \widehat\omega_P \left(\operatorname{Exp}\_{\mathrm f}(itY)\right) = \operatorname{Exp}\_{\mathrm f}(-Vt^2/2). } \tag{14} \\]

Every step is an algebraic identity involving finite words. The infinite formal series is legitimate because each coefficient involves only finitely many terms.

In particular, the Wick identity is derived from the state and CCR, not introduced as an additional Gaussian-state axiom.

### 3.5 The complete two-point function

By Hermiticity and \\(t^\dagger=t\\),

\\[ \operatorname{Exp}\_{\mathrm f}(itX_J(x))^\dagger = \operatorname{Exp}\_{\mathrm f}(-itX_J(x)). \\]

Adjoints reverse factor order. Since charge words commute with oscillator words,

\\[ \begin{aligned} W_J(t,x)^\dagger W_J(t,y) ={}&L^{-2}K_J(x)^\dagger K_J(y)\\\ &\times\operatorname{Exp}\_{\mathrm f}(-itX_J(x)) \operatorname{Exp}\_{\mathrm f}(itX_J(y)). \end{aligned} \\]

Equation (7) allows the binomial formal-exponential identity:

\\[ \operatorname{Exp}\_{\mathrm f}(-itX_J(x)) \operatorname{Exp}\_{\mathrm f}(itX_J(y)) = \operatorname{Exp}\_{\mathrm f}(itY_J). \\]

Hence, exactly as a formal operator identity,

\\[ W_J(t,x)^\dagger W_J(t,y) = L^{-2}K_J(x)^\dagger K_J(y) \operatorname{Exp}\_{\mathrm f}(itY_J). \tag{15} \\]

Applying the factorized charge/oscillator functional, then (5), (10), and (14), yields Equation (1).

There is no unstated reordering of two noncommuting charge operators, no missing BCH scalar, and no analytic limit.

### 3.6 Coefficient audit

Let

\\[ \chi_J=\zeta^{a_J(N)(y-x)}, \qquad d=D_1(x,y), \qquad G=g_J. \\]

The proposed answer expands as

\\[ \frac{\chi_J}{L^2} \left( 1-2Gdt^2+2G^2d^2t^4+O(t^6) \right), \\]

where \\(O(t^6)\\) here denotes terms of formal degree at least six, not an analytic remainder estimate.

| Coefficient      | Exact result                  |
| ---------------- | ----------------------------- |
| \\([t^0]\\)      | \\(L^{-2}\chi_J\\)            |
| \\([t^1]\\)      | \\(0\\)                       |
| \\([t^2]\\)      | \\(-2L^{-2}\chi_JGd\\)        |
| \\([t^3]\\)      | \\(0\\)                       |
| \\([t^4]\\)      | \\(2L^{-2}\chi_JG^2d^2\\)     |
| \\([t^{2k}]\\)   | \\(L^{-2}\chi_J(-2Gd)^k/k!\\) |
| \\([t^{2k+1}]\\) | \\(0\\)                       |

The fourth-order coefficient also follows independently from

\\[ \omega_P(Y_J^4) =3V_J^2=48G^2d^2, \\]

so

\\[ \frac{i^4}{4!}\omega_P(Y_J^4) =\frac{48}{24}G^2d^2 =2G^2d^2. \\]

This tests the factorial structure rather than merely matching the quadratic term.

At equal positions, \\(Y_J=0\\), and the complete identity reduces to

\\[ \boxed{ \widehat\omega\_{P,N} \left(W_J(t,x)^\dagger W_J(t,x)\right) =L^{-2}. } \tag{16} \\]

Indeed, \\(W_J^\dagger W_J=L^{-2}I\\) directly in the formal algebra. The Weyl-type vertex is a formally unitary exponential multiplied by \\(L^{-1}\\).

## 4. Normal ordering and the physical interpretation

Normal ordering requires specifying which annihilators define the reference vacuum. Here there are two distinct choices: dressed ordering relative to \\(\omega_P\\), and bare ordering relative to \\(\omega_0\\).

### 4.1 Normal ordering with respect to dressed modes

Write

\\[ X_J(x)=C_J(x)+A_J(x), \qquad A_J(x)=C_J(x)^\dagger, \\]

where \\(C_J\\) contains only dressed creators.

Define

\\[ H_M=\sum\_{m=1}^M\frac1m. \\]

The oscillator algebra gives

\\[ [A_J(x),C_J(x)] =2g_JH_M I. \\]

The central-commutator BCH identity, interpreted coefficientwise, then gives

\\[ \operatorname{Exp}\_{\mathrm f}(itX_J) = \operatorname{Exp}\_{\mathrm f}(itC_J) \operatorname{Exp}\_{\mathrm f}(itA_J) \operatorname{Exp}\_{\mathrm f}(-g_JH_Mt^2). \tag{17} \\]

Let the dressed normal-ordered vertex be

\\[ W_J^{:\ :}(t,x) = L^{-1}K_J(x) \operatorname{Exp}\_{\mathrm f}(itC_J(x)) \operatorname{Exp}\_{\mathrm f}(itA_J(x)). \\]

Equation (17) shows that

\\[ \boxed{ W_J^{:\ :}(t,x) = \operatorname{Exp}\_{\mathrm f}(g_JH_Mt^2) W_J(t,x). } \tag{18} \\]

Thus the normal-ordered two-point function is

\\[ \boxed{ \begin{aligned} &\widehat\omega\_{P,N} \left(W_J^{:\ :}(t,x)^\dagger W_J^{:\ :}(t,y)\right)\\\ &=\frac{\chi_J}{L^2} \operatorname{Exp}\_{\mathrm f} \left[ 2g_J\left(H_M-D_1(x,y)\right)t^2 \right]\\\ &=\frac{\chi_J}{L^2} \operatorname{Exp}\_{\mathrm f} \left[ 2g_Jt^2 \sum\_{m=1}^M \frac{\cos(2\pi m(x-y)/L)}m \right]. \end{aligned} } \tag{19} \\]

Unlike the Weyl-type vertex, the normal-ordered vertex is not formally unitary. Its equal-point two-point function is

\\[ L^{-2}\operatorname{Exp}\_{\mathrm f}(2g_JH_Mt^2). \\]

Normal ordering therefore changes the correlator by a genuine cutoff-dependent scalar, even at finite \\(M\\).

### 4.2 Bare normal ordering gives a different prefactor

There is a useful additional algebraic observation that makes the distinction particularly clear.

Let \\(Q_R^{(0)},Q_L^{(0)}\\) be the same oriented fields constructed from the undressed \\(C,A\\). The Bogoliubov definitions imply

\\[ \begin{aligned} Q_R&=cQ_R^{(0)}+sQ_L^{(0)},\\\ Q_L&=cQ_L^{(0)}+sQ_R^{(0)}. \end{aligned} \\]

Since \\((c-s)(c+s)=1\\),

\\[ \boxed{ \begin{aligned} X_D&=Q_R^{(0)}+Q_L^{(0)},\\\ X_S&=Q_R^{(0)}-Q_L^{(0)}. \end{aligned} } \tag{20} \\]

Thus, viewed as elements of the original CCR algebra, these two vertex exponents are actually independent of \\(c,s\\). The interaction parameter enters their correlations through the state \\(\omega_P\\).

This is not a contradiction; it is the algebraic analogue of holding an observable fixed while varying the state.

With bare rather than dressed creator/annihilator normal ordering, the self-contraction is \\(2H_M\\), rather than \\(2g_JH_M\\). Consequently,

\\[ W_J^{:\ :\_0}(t,x) =\operatorname{Exp}\_{\mathrm f}(H_Mt^2)W_J(t,x), \\]

and

\\[ \boxed{ \widehat\omega\_{P,N} \left( W_J^{:\ :\_0}(t,x)^\dagger W_J^{:\ :\_0}(t,y) \right) = \frac{\chi_J}{L^2} \operatorname{Exp}\_{\mathrm f} \left[(2H_M-2g_JD_1(x,y))t^2\right]. } \tag{21} \\]

Equations (19) and (21) agree in the free case \\(g_J=1\\), but generally differ.

Therefore the instruction to “normal-order the vertex” is mathematically incomplete without identifying the reference splitting.

Moreover, neither normalization supplies an exact finite-CAR electron-field dictionary. The appropriate physical prefactor is not determined uniquely by the oscillator CCR, because it also depends on the microscopic field normalization, regulator, zero-mode conventions, and the desired operator comparison.

## 5. Dependency map and minimal theorem list

The formal correlator theorem has a short algebraic dependency structure. It does not require any fermionic energy-budget identification.

Uncompressed CCR algebra

Polynomial representation, adjoints, and positive vacuum

Oscillator branch

Bogoliubov automorphism, dressed contractions, Wick recurrence, field commutators

Charge branch

Signed bilateral shifts, source phases, ordered adjoints

Formal-series product and coefficientwise evaluation

No convergence assumption

Formal CDW/SC correlator identity

Equation (1), all coefficients

Separate physical bridge

Finite-CAR operator comparison + state comparison + projection residual control

Not supplied by the formal correlator theorem

The minimal theorem list, formulated in ordinary mathematics, is:

1\. Positive oscillator state: The polynomial representation satisfies the CCR and adjoint identities, and \\(\omega_P=\omega_0\circ\beta^{-1}\\) is a normalized positive functional with the dressed contractions (2).

2\. Ordered charge multiplication: The bilateral charge shifts are unitary on the algebraic charge carrier, and Equation (5) holds for both ordered Klein words.

3\. Field commutators and variances: The fields \\(X_J\\) are Hermitian, satisfy Equation (7), and have difference variance (10).

4\. Formal Wick theorem: Every Hermitian linear combination of dressed oscillator generators satisfies the moment recurrence (13) and Gaussian identity (14).

5\. Coefficientwise vertex theorem: Formal exponentials obey the product law whenever their exponents commute, and the joint charge/oscillator state evaluates the resulting product to Equation (1).

A sixth, optional mathematical theorem would establish the corresponding normal-ordering transformations (18)–(21). These follow from the same CCR, but should remain separate statements because they describe different definitions of the vertex.

### Which results belong to which layer?

The provided baseline establishes the finite current and energy-budget foundations and the CH19/A08 state infrastructure. The specified commit's CH20 validation record describes the finite CH20 package as promoted, while explicitly leaving formal vertices and full Wick/state transport outside that acceptance.

The Chapter 20.2 manuscript supplies candidate mathematical proofs of the formal-charge construction. The derivations in this answer independently establish the identity under its abstract hypotheses. They do not establish that the corresponding Lean declarations exist, compile, or have passed Core acceptance.

The dependency distinction is substantive: a correct mathematical manuscript proof is not a formalized theorem, and a formally verified finite-CAR theorem is not automatically a proof of an uncompressed oscillator identity.

### The strongest useful physical target

For version 1, the strongest currently justified conclusion is the exact formal model theorem (1), accompanied by an explicitly unresolved physical comparison.

A future physical comparison would need to specify an admissible source sector \\(B(N,K)\\), the appropriate target charge sector \\(B(N+\delta_J,K')\\), and actual finite-CAR operators \\(T_J(x)\\). It would also need a precisely defined finite-budget representation of a vertex candidate \\(V_J(x)\\).

The comparison should then address the difference between the corresponding ordered kernels, rather than assume equality.

One logically sound possibility is to establish an operator identification under the CH14 cyclic-intertwining criterion. Another is to prove a quantitative estimate on the difference of matrix elements, with explicit projection residuals and state-comparison hypotheses.

Both are stronger physical requirements than Equation (1). Moreover, because \\(t\\) is formal, comparing \\(T_J\\) directly with \\(W_J(1,x)\\) would require an additional definition: either a controlled finite polynomial approximation or an analytic realization with justified evaluation at \\(t=1\\).

The existing charge-sector isometries and current identities do not by themselves supply such an evaluation.

## 6. Finite example, obstructions, and unresolved questions

### 6.1 Four-site formal calculation

Choose

\\[ L=4,\quad h=2,\quad M=1,\quad c=1,\quad s=0,\quad N=(0,0), \\]

with \\(x=0\\), \\(y=1\\).

Then

\\[ \zeta=i,\qquad g_D=g_S=1,\qquad D_1(0,1)=1. \\]

The source charge exponents are

\\[ a_D(0,0)=-1, \qquad a_S(0,0)=0. \\]

Therefore

\\[ \boxed{ \widehat\omega\_{P,0}(W_D(t,0)^\dagger W_D(t,1)) = -\frac{i}{16}\operatorname{Exp}\_{\mathrm f}(-2t^2) } \\]

and

\\[ \boxed{ \widehat\omega\_{P,0}(W_S(t,0)^\dagger W_S(t,1)) = \frac1{16}\operatorname{Exp}\_{\mathrm f}(-2t^2). } \\]

Both use the same Gaussian coefficients,

\\[ 1-2t^2+2t^4-\frac43t^6+\cdots, \\]

but differ by the source charge phase.

These identities can also be checked directly from two oscillator modes with variance \\(V_D=V_S=4\\). Thus the example is non-vacuous: it tests the charge phase, chiral multiplicity, second moment, and fourth moment simultaneously.

It does not test interacting finite-CAR bosonization. Here \\(s=0\\), the oscillator model remains uncompressed, and the formal parameter is not evaluated.

### 6.2 Explicit finite-CAR normalization obstruction

Consider the same \\(L=4\\) lattice, but now use actual finite-CAR position fields. Choose a product Slater state with two occupied momentum orbitals per species.

Translation invariance gives

\\[ \langle n\_{R,x}\rangle =\langle n\_{L,x}\rangle=\frac12. \\]

Because the two species occupy independent Slater factors,

\\[ \begin{aligned} \langle O_D(x)^\dagger O_D(x)\rangle &=\langle n\_{L,x}(1-n\_{R,x})\rangle =\frac14,\\\ \langle O_S(x)^\dagger O_S(x)\rangle &=\langle n\_{R,x}n\_{L,x}\rangle =\frac14. \end{aligned} \\]

The formal Weyl vertices instead satisfy

\\[ \widehat\omega\_{P,N}(W_J(t,x)^\dagger W_J(t,x)) =\frac1{16}. \\]

The values differ by a factor of four.

This is a counterexample to identifying the two constructions as already normalized, state-preserving physical observables in that free finite-state example. It is not a no-go theorem against every possible normalization or a suitably modified vertex dictionary.

In particular, multiplying a candidate vertex by two would repair this one equal-point numerical discrepancy. It would not prove equality at distinct positions or establish the required operator intertwining.

More generally, at fixed \\(x\\),

\\[ O_D(x)^\dagger O_D(x) =n\_{L,x}(1-n\_{R,x}) \\]

and

\\[ O_S(x)^\dagger O_S(x) =n\_{R,x}n\_{L,x}. \\]

Neither operator is proportional to the identity on the full finite-CAR Fock space. In contrast, the formal Weyl vertex obeys

\\[ W_J(t,x)^\dagger W_J(t,x)=L^{-2}I. \\]

Thus a global star-preserving identification of these particular operators is impossible without changing the operators, restricting the carrier, or weakening the comparison. This is a stronger algebraic obstruction than the single-state normalization discrepancy.

### 6.3 Projection and finite-dimensional limitations

Any attempt to transport the formal CCR to an entire nonzero finite-dimensional budget space encounters

\\[ \operatorname{tr}[A,C]=0, \qquad \operatorname{tr}(mI)=m\dim B\ne0. \\]

Therefore global exact CCR cannot hold there.

For an intermediate projection \\(P_m\\),

\\[ P_tABP_s-P_tAP_mBP_s = P_tA(I-P_m)BP_s. \\]

Unless the discarded-channel term vanishes under separately verified hypotheses, the compressed product is not the restriction of the uncompressed product. This affects the contractions required by a Wick argument as well as products of exponentials.

The A08 compressed common-kernel example reinforces the warning: its absence of a common dressed vacuum excludes that particular squeezed-vacuum construction, not the existence of every finite interacting ground state.

### 6.4 Remaining clarifying questions

The formal identity itself does not require additional definitions. The remaining questions concern its intended physical use.

First, which normal-ordering convention is intended for the physical vertex correspondence: bare sea ordering or dressed-state ordering? Equations (19) and (21) show that these are inequivalent at \\(s\ne0\\).

Second, which exact zero-mode and twist conventions should be carried from CH14 into the proposed physical CDW/SC field dictionary? The present charge words are well-defined for integer exponents on \\(\mathbb Z/L\mathbb Z\\), but the species twists of finite-CAR fields can require additional phases and lifted spatial-field conventions. The present formal correlator cannot determine those missing physical phases.

Third, what is the intended comparison state? The algebraic functional \\(\omega\_{P,N}\\) is completely defined, but a physical finite-CAR ground state must be specified independently. Neither the finite scalar comparison at \\(s=0\\) nor the compressed no-vacuum witness determines the generic interacting state.

Fourth, should the physical bridge seek an exact operator equality on a margin-controlled budget, or a quantitative comparison of selected matrix elements? These are different research questions. The former requires the full CH14 physical obligations; the latter may be feasible with weaker assumptions, but still needs control of discarded channels and state mismatch.

### 6.5 Verified literature

The following references are appropriate background for the distinction between bosonic current algebra, Klein factors, finite-size bosonization, and physical correlators. Their bibliographic identifiers were checked against publisher, institutional, or primary-record metadata.

1\. Daniel C. Mattis and Elliott H. Lieb, Exact Solution of a Many-Fermion System and Its Associated Boson Field, Journal of Mathematical Physics 6, 304–312 (1965). DOI: [10.1063/1.1704281](https://doi.org/10.1063/1.1704281?utm_source=chatgpt.com).&#x20;

[image](https://www.google.com/s2/favicons?domain=https://collaborate.princeton.edu\&sz=32)

Princeton University

+1



2\. F. D. M. Haldane, 'Luttinger liquid theory' of one-dimensional quantum fluids. I. Properties of the Luttinger model and their extension to the general 1D interacting spinless Fermi gas, Journal of Physics C: Solid State Physics 14, 2585–2609 (1981). DOI: [10.1088/0022-3719/14/19/010](https://doi.org/10.1088/0022-3719/14/19/010?utm_source=chatgpt.com).&#x20;

[image](https://www.google.com/s2/favicons?domain=https://collaborate.princeton.edu\&sz=32)

Princeton University



3\. Jan von Delft and Herbert Schoeller, Bosonization for Beginners — Refermionization for Experts, Annalen der Physik 510, 225–305 (1998). DOI: [10.1002/andp.19985100401](https://doi.org/10.1002/andp.19985100401?utm_source=chatgpt.com); arXiv: [cond-mat/9805275](https://arxiv.org/abs/cond-mat/9805275?utm_source=chatgpt.com). Particularly relevant for finite-size zero modes and Klein factors.&#x20;

[image](https://www.google.com/s2/favicons?domain=https://onlinelibrary.wiley.com\&sz=32)

Wiley Online Library

+1



4\. Thierry Giamarchi, Quantum Physics in One Dimension, Oxford University Press. DOI: [10.1093/acprof:oso/9780198525004.001.0001](https://doi.org/10.1093/acprof:oso/9780198525004.001.0001?utm_source=chatgpt.com). Relevant for physical normal-ordering prescriptions and Luttinger-liquid correlations.&#x20;

[image](https://www.google.com/s2/favicons?domain=https://academic.oup.com\&sz=32)

Oxford Academic



These references motivate and contextualize the bosonization framework. None replaces the explicit finite algebraic derivation performed above.

## Final assessment

The Chapter 20.2 formal correlator is mathematically sound for the proposed uncompressed oscillator/charge model. The source-charge shift, opposite chiral orientations, Gaussian variance, BCH cancellation, and factorial coefficients are mutually consistent.

The strongest justified statement for Bosonize-Lean version 1 is the exact coefficientwise formal vertex theorem, with normalization and normal-ordering conventions kept explicit.

The unresolved problem is not the Gaussian calculation. It is the physical identification of these formal vertices with finite-CAR CDW/SC observables and their interacting state correlations. The equal-point operator and scalar discrepancies demonstrate why that identification cannot be inferred from the formal identity, Haldane completeness, or current-algebra agreement alone.

No code changes, chapter-scope decisions, or claims of Lean verification follow from this review.
