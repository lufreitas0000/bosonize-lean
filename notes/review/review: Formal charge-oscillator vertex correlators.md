# Independent mathematical review: Formal charge/oscillator vertex correlators

Bosonize-Lean v1 — Chapter 20b

Reference snapshot: `40dea8bfbdc849417c072e490480d4f72536116a`, October 17, 2026.

Sources examined: the supplied mathematical baseline, the uploaded monograph Constructive 1+1D Lattice Bosonization, and the corresponding Chapter 20.2 manuscript in the GitHub repository.

## 1. Verdict

The proposed CDW and SC correlator identities are mathematically correct as coefficientwise identities on the specified auxiliary charge–oscillator algebra. They do not require analytic exponentiation, a finite-dimensional CCR representation, or identification with physical CAR operators.

For \\(J\in\\{D,S\\}\\), define

\\[ \begin{aligned} a_D(N)&=N_L-N_R-1,\\\ a_S(N)&=N_R+N_L,\\\ g_D&=g=(c-s)^2,\\\ g_S&=g^{-1}=(c+s)^2. \end{aligned} \\]

Then, under the hypotheses in the prompt,

\\[ \boxed{ \begin{aligned} &\widehat\omega\_{P,N} \left(W_J(t,x)^\dagger W_J(t,y)\right)\\\ &\qquad = \frac{\zeta^{a_J(N)(y-x)}}{L^2} \operatorname{Exp}\_{\mathrm f} \left(-2g_JD_1(x,y)t^2\right). \end{aligned} } \tag{1} \\]

This is proved below directly from the CCR, the source-charge action, and an explicit Gaussian recurrence.

### Classification of results

| Statement                                                                      | Verdict                                                                       |
| ------------------------------------------------------------------------------ | ----------------------------------------------------------------------------- |
| Hermiticity of \\(X_D,X_S\\)                                                   | Proved here                                                                   |
| Same-channel commutators vanish                                                | Proved here                                                                   |
| No BCH correction in \\(W_J^\dagger(x)W_J(y)\\)                                | Proved here                                                                   |
| Charge phases in (1), including the positive SC exponent                       | Proved here                                                                   |
| Gaussian coefficients at every formal order                                    | Proved here                                                                   |
| Positivity of the underlying oscillator/charge functional                      | Follows from the specified algebraic representations                          |
| Appendix E.14's negative SC phase                                              | Contradicted by the stated charge words                                       |
| Identification with arbitrary finite interacting CAR correlators               | Unresolved; not implied                                                       |
| Universal equality with the finite-CAR bilinears under the given normalization | Contradicted by a finite free-state example                                   |
| Normal-ordered physical vertex interpretation                                  | Conditional on an ordering prescription and further operator/state comparison |

### Manuscript discrepancy

Chapter 20.2, equations (20.78)–(20.79), agrees with (1). However, Appendix E, equation (E.14), writes the SC phase with a negative exponent:

\\[ \zeta^{-(N_R+N_L)(y-x)}. \\]

That sign is inconsistent with

\\[ K_S(x)=F_RF_L\zeta^{(N_R+N_L)x}. \\]

The positive exponent is correct for \\(K_S(x)^\dagger K_S(y)\\). Appendix E.14 should not be used as an independent justification of the opposite convention.&#x20;

main.pdf



The manuscript calls the correlator theorem a draft. The reported Core promotions are accepted as the supplied repository baseline, but this review makes no additional claim of Lean verification.

## 2. Mathematical objects, domains, and ordering

### 2.1 Oscillator algebra and state

Let

\\[ \mathcal P =\mathbb C[X\_{\nu m}:\nu\in\\{R,L\\},\ 1\le m\le M], \qquad M\ge1. \\]

The carrier is an unbounded-degree polynomial space. Creation and annihilation act by

\\[ C\_{\nu m}p=X\_{\nu m}p, \qquad A\_{\nu m}p=m\\,\frac{\partial p}{\partial X\_{\nu m}}. \\]

Consequently,

\\[ [A\_{\nu m},C\_{\eta n}] =m\delta\_{\nu\eta}\delta\_{mn}I, \qquad [C,C]=[A,A]=0. \\]

The weighted monomial pairing is positive definite, \\(A\_{\nu m}^\dagger=C\_{\nu m}\\), and the polynomial vacuum is

\\[ \omega_0(a)=\langle 1,\pi_0(a)1\rangle. \\]

These are algebraic constructions; no Hilbert-space completion is needed for the finite-order calculations.

For real \\(c,s\\) with \\(c^2-s^2=1\\), let \\(\beta\\) be the given Bogoliubov automorphism, and define

\\[ \omega_P=\omega_0\circ\beta^{-1}. \\]

The inverse is essential. In this state, the dressed generators \\(\widetilde C=\beta(C)\\), \\(\widetilde A=\beta(A)\\) have the ordered contractions

\\[ \begin{aligned} \omega_P(\widetilde A\_{\nu m}\widetilde C\_{\eta n})  &=m\delta\_{\nu\eta}\delta\_{mn},\\\ \omega_P(\widetilde C\_{\nu m}\widetilde A\_{\eta n})  &=0,\\\ \omega_P(\widetilde A\widetilde A)  &=\omega_P(\widetilde C\widetilde C)=0. \end{aligned} \tag{2} \\]

Thus \\(\omega_P\\) is the vacuum for the dressed annihilators, not the bare annihilators. Reversing the pullback changes the contraction convention and invalidates the argument as stated.

### 2.2 Charge carrier and Klein factors

Define the algebraic charge space

\\[ \mathcal C=\mathbb C^{(\mathbb Z^2)}, \qquad \langle N'|N\rangle=\delta\_{N'N}. \\]

The parentheses mean finite support. The charge operators act diagonally, and

\\[ F_R|N_R,N_L\rangle=|N_R-1,N_L\rangle, \\]

\\[ F_L|N_R,N_L\rangle =(-1)^{N_R}|N_R,N_L-1\rangle. \\]

Their adjoints are the inverse signed shifts. These maps preserve finite support and are algebraically unitary.

The total carrier is

\\[ \mathcal H\_{\rm aux}=\mathcal C\otimes\mathcal P. \\]

Charge and oscillator operators act on separate tensor factors and commute. The positive functional is

\\[ \omega\_{P,N} =\omega\_{{\rm ch},N}\otimes\omega_P, \qquad \omega\_{{\rm ch},N}(B)=\langle N|B|N\rangle. \tag{3} \\]

This is an auxiliary infinite-dimensional model, distinct from the finite-CAR space \\(B(N,K)\\).

The simplified Klein-factor convention in the prompt differs from the \\(h\\)-dependent convention printed in Chapter 20.2. They are related by a diagonal sign gauge. For example, a gauge with diagonal entries

\\[ (-1)^{ N_R(N_R-1)/2+hN_R+N_L(N_L-1)/2 } \\]

transforms the manuscript shifts into the simplified ones. The fixed-source two-point charge phases are gauge invariant. This equivalence does not identify the auxiliary charge carrier with finite fermionic sectors.

### 2.3 Formal exponential and adjoint

Let \\(t\\) be a central, self-adjoint indeterminate. For \\(X\\) in the operator algebra,

\\[ \operatorname{Exp}\_{\mathrm f}(itX) =\sum\_{n=0}^{\infty}\frac{i^nt^nX^n}{n!}. \\]

Every coefficient is a finite algebraic expression. The star operation is coefficientwise and sends \\(i\\) to \\(-i\\).

If \\(X^\dagger=X\\),

\\[ \operatorname{Exp}\_{\mathrm f}(itX)^\dagger =\operatorname{Exp}\_{\mathrm f}(-itX). \tag{4} \\]

The formal evaluator is

\\[ \widehat\omega\_{P,N} \left(\sum\_{n\ge0}a_nt^n\right) =\sum\_{n\ge0}\omega\_{P,N}(a_n)t^n. \\]

It is a \\(\mathbb C[[t]]\\)-linear evaluator, not an ordinary scalar-valued state on arbitrary formal series. No substitution \\(t=1\\) is used.

## 3. Derivation of the correlator

### 3.1 Hermiticity

For \\(\epsilon_R=1\\), \\(\epsilon_L=-1\\), define

\\[ Q\_\nu(x) =\sum\_{m=1}^M \frac{ \zeta^{-\epsilon\_\nu mx}\widetilde C\_{\nu m} +\zeta^{\epsilon\_\nu mx}\widetilde A\_{\nu m} }{m}. \\]

Since \\(|\zeta|=1\\), and dressed creation and annihilation are mutual adjoints,

\\[ Q\_\nu(x)^\dagger=Q\_\nu(x). \\]

The coefficients \\(c-s\\) and \\(c+s\\) are real, so

\\[ X_D(x)^\dagger=X_D(x), \qquad X_S(x)^\dagger=X_S(x). \tag{5} \\]

These are exact algebraic statements.

A useful structural observation follows by introducing the corresponding bare sums \\(q_R,q_L\\). The opposite chiral Fourier orientations give

\\[ Q_R=cq_R+sq_L, \qquad Q_L=cq_L+sq_R. \\]

Hence

\\[ \begin{aligned} X_D&=(c-s)(Q_R+Q_L)=q_R+q_L,\\\ X_S&=(c+s)(Q_R-Q_L)=q_R-q_L. \end{aligned} \tag{6} \\]

The last equalities use \\((c-s)(c+s)=1\\).

Thus, when expressed in bare generators, both \\(X_D\\) and \\(X_S\\) are independent of \\(c,s\\). Their interacting covariance comes from the state \\(\omega_P\\), not from additional dependence of the bare operator expressions. This prevents double-counting the Bogoliubov transformation.

### 3.2 Commutators and BCH

Let

\\[ \theta_m(x,y)=\frac{2\pi m(x-y)}L. \\]

Directly using (2) and the CCR,

\\[ [Q_R(x),Q_R(y)] =2i\sum\_{m=1}^M\frac{\sin\theta_m(x,y)}m\\,I, \\]

whereas the reversed left-chiral orientation gives

\\[ [Q_L(x),Q_L(y)] =-2i\sum\_{m=1}^M\frac{\sin\theta_m(x,y)}m\\,I. \\]

Mixed dressed-chirality commutators vanish. Therefore

\\[ [Q_R(x)\pm Q_L(x),Q_R(y)\pm Q_L(y)]=0 \\]

when the same sign is used in both factors, and

\\[ \boxed{ [X_J(x),X_J(y)]=0,\qquad J=D,S. } \tag{7} \\]

This cancellation is exact at every finite \\(M\\). It does not rely on a continuum limit.

For contrast, the mixed-channel commutator is generally nonzero:

\\[ [X_D(x),X_S(y)] =4i\sum\_{m=1}^M\frac{\sin\theta_m(x,y)}m\\,I. \tag{8} \\]

Thus the result establishes same-channel commutativity, not mutual commutativity of all vertex phases.

Now define

\\[ Y_J=X_J(y)-X_J(x). \\]

By (7), the coefficientwise binomial theorem gives

\\[ \operatorname{Exp}\_{\mathrm f}(-itX_J(x)) \operatorname{Exp}\_{\mathrm f}(itX_J(y)) =\operatorname{Exp}\_{\mathrm f}(itY_J). \tag{9} \\]

There is no BCH scalar correction. Indeed, the usual central-commutator expression would contain

\\[ \frac12[-itX_J(x),itX_J(y)] =\frac{t^2}{2}[X_J(x),X_J(y)]=0. \\]

Using this simplification for an individual chirality would be incorrect: its spatial commutator is generally nonzero and produces an ordered phase.

### 3.3 Exact source-charge phases

Set

\\[ Z_D(x)=\zeta^{(N_L-N_R-1)x}, \qquad Z_S(x)=\zeta^{(N_R+N_L)x}, \\]

and

\\[ U_D=F_R^\dagger F_L, \qquad U_S=F_RF_L. \\]

Then \\(K_J(x)=U_JZ_J(x)\\), with the diagonal phase acting first.

The shifts act as

\\[ U_D|N\rangle=(-1)^{N_R}|N+e_R-e_L\rangle, \\]

\\[ U_S|N\rangle=(-1)^{N_R}|N-e_R-e_L\rangle. \tag{10} \\]

Thus the charge shifts are exactly those of the proposed CAR channels.

More explicitly,

\\[ \begin{aligned} K_D(x)|N\rangle &=(-1)^{N_R}\zeta^{a_D(N)x}   |N+e_R-e_L\rangle,\\\ K_S(x)|N\rangle &=(-1)^{N_R}\zeta^{a_S(N)x}   |N-e_R-e_L\rangle. \end{aligned} \tag{11} \\]

Because the \\(U_J\\) are unitary,

\\[ K_J(x)^\dagger K_J(y) =Z_J(x)^\dagger U_J^\dagger U_JZ_J(y) =Z_J(x)^\dagger Z_J(y). \\]

Therefore

\\[ \boxed{ K_J(x)^\dagger K_J(y)|N\rangle =\zeta^{a_J(N)(y-x)}|N\rangle. } \tag{12} \\]

Both Klein signs cancel, and the source charge is the original \\(N\\). There is no additional source-shift phase in this ordering.

The opposite ordering is different. Writing the shifts as \\(q_D=(1,-1)\\), \\(q_S=(-1,-1)\\), one obtains

\\[ K_J(x)K_J(y)^\dagger|N\rangle =\zeta^{a_J(N-q_J)(x-y)}|N\rangle, \\]

and, in both channels,

\\[ a_J(N-q_J)=a_J(N)+2. \tag{13} \\]

This is why source-phase placement and the order of the correlator cannot be changed casually.

Equation (12) also settles the SC sign discrepancy: with the definitions given, the exponent is \\(+(N_R+N_L)(y-x)\\).

### 3.4 Oscillator variance

The only nonzero dressed contraction is \\(\omega_P(\widetilde A\widetilde C)\\), so

\\[ \omega_P(Q_R(x)Q_R(y)) =\sum\_{m=1}^M\frac{e^{i\theta_m(x,y)}}m, \\]

\\[ \omega_P(Q_L(x)Q_L(y)) =\sum\_{m=1}^M\frac{e^{-i\theta_m(x,y)}}m. \tag{14} \\]

The two branches have conjugate ordered kernels. Each difference has variance

\\[ \begin{aligned} &\omega_P\bigl((Q\_\nu(y)-Q\_\nu(x))^2\bigr)\\\ &\quad= \omega_P(Q\_\nu(y)^2)+\omega_P(Q\_\nu(x)^2)\\\ &\qquad-\omega_P(Q\_\nu(y)Q\_\nu(x)) -\omega_P(Q\_\nu(x)Q\_\nu(y))\\\ &\quad=2D_1(x,y). \end{aligned} \\]

Cross-chirality contractions vanish. Consequently,

\\[ \boxed{ V_J:=\omega_P(Y_J^2)=4g_JD_1(x,y). } \tag{15} \\]

Also \\(\omega_P(Y_J)=0\\). Since \\(M\\) is finite and the \\(m=1\\) term is present,

\\[ D_1(x,y)\ge0, \\]

with equality precisely at \\(x=y\\) modulo \\(L\\).

### 3.5 Explicit Gaussian recurrence

The only Wick-type result needed is the moment formula for a single Hermitian linear combination of dressed oscillators. A general ordered Wick theorem is unnecessary for (1).

Pull \\(Y_J\\) back by \\(\beta^{-1}\\), and write the resulting operator as

\\[ Y=C_f+A\_{\bar f}, \\]

where

\\[ C_f=\sum_j f_jC_j, \qquad A\_{\bar f}=\sum_j\overline{f_j}A_j, \\]

with \\(j=(\nu,m)\\). Let

\\[ V=\sum_j m_j|f_j|^2. \\]

Then

\\[ [A\_{\bar f},Y]=VI, \qquad A\_{\bar f}1=0, \qquad \langle1,C_fp\rangle=0 \\]

for every polynomial \\(p\\).

Because \\(V\\) is central,

\\[ [A\_{\bar f},Y^n]=nVY^{n-1}. \\]

It follows that

\\[ \begin{aligned} \omega_0(Y^{n+1}) &=\langle1,(C_f+A\_{\bar f})Y^n1\rangle\\\ &=\langle1,A\_{\bar f}Y^n1\rangle\\\ &=\langle1,[A\_{\bar f},Y^n]1\rangle\\\ &=nV\\,\omega_0(Y^{n-1}). \end{aligned} \tag{16} \\]

With \\(\omega_0(I)=1\\) and \\(\omega_0(Y)=0\\), induction gives

\\[ \boxed{ \omega_P(Y_J^{2k+1})=0, \qquad \omega_P(Y_J^{2k}) =\frac{(2k)!}{2^kk!}V_J^k. } \tag{17} \\]

This explicitly derives the required Gaussian recurrence, including its factorials. There is no appeal to a probabilistic Gaussian measure or an unproved analytic exponential identity.

Therefore

\\[ \begin{aligned} \widehat\omega_P\\!\left( \operatorname{Exp}\_{\mathrm f}(itY_J)\right) &=\sum\_{k=0}^{\infty} \frac{(-1)^kt^{2k}}{(2k)!} \frac{(2k)!}{2^kk!}V_J^k\\\ &=\operatorname{Exp}\_{\mathrm f} \left(-\frac{V_Jt^2}{2}\right)\\\ &=\operatorname{Exp}\_{\mathrm f} \left(-2g_JD_1(x,y)t^2\right). \end{aligned} \tag{18} \\]

### 3.6 Assembly and coefficient checks

The vertex adjoint reverses product order:

\\[ W_J(t,x)^\dagger =L^{-1}\operatorname{Exp}\_{\mathrm f}(-itX_J(x)) K_J(x)^\dagger. \\]

Charge and oscillator factors commute because they are independent tensor factors. Combining (9), (12), and (18) therefore proves equation (1).

Writing

\\[ \chi_J(N;x,y)=\zeta^{a_J(N)(y-x)}, \qquad D=D_1(x,y), \\]

the first coefficients are

\\[ \widehat\omega\_{P,N} (W_J^\dagger(t,x)W_J(t,y)) = \frac{\chi_J}{L^2} \left[ 1-2g_JDt^2+2g_J^2D^2t^4+O(t^6) \right], \tag{19} \\]

where \\(O(t^6)\\) denotes terms in \\(t^6\mathbb C[[t]]\\).

| Coefficient | Exact value                 |
| ----------- | --------------------------- |
| \\(t^0\\)   | \\(L^{-2}\chi_J\\)          |
| \\(t^1\\)   | \\(0\\)                     |
| \\(t^2\\)   | \\(-2L^{-2}\chi_Jg_JD\\)    |
| \\(t^4\\)   | \\(2L^{-2}\chi_Jg_J^2D^2\\) |

In particular, the fourth coefficient follows independently from \\(\omega_P(Y_J^4)=3V_J^2\\):

\\[ \frac{i^4}{4!}\omega_P(Y_J^4) =\frac{3(4g_JD)^2}{24} =2g_J^2D^2. \\]

The correlator also has the required Hermitian symmetry,

\\[ \overline{C_J(x,y;t)}=C_J(y,x;t), \tag{20} \\]

coefficientwise, because \\(D_1(x,y)=D_1(y,x)\\) and \\(|\zeta|=1\\). It need not be real away from coincident points.

At \\(x=y\\),

\\[ \widehat\omega\_{P,N} (W_J(t,x)^\dagger W_J(t,x))=L^{-2}. \tag{21} \\]

These checks establish normalization and all coefficients of the stated formal series, not just a low-order approximation.

## 4. Normal ordering and the physical interpretation

The theorem above concerns Weyl-type formal exponentials. Normal ordering changes the correlator.

Define the harmonic cutoff sum

\\[ H_M=\sum\_{m=1}^M\frac1m, \\]

and the cosine kernel

\\[ C_M(x-y)=\sum\_{m=1}^M \frac{\cos(2\pi m(x-y)/L)}m. \\]

Then \\(D_1(x,y)=H_M-C_M(x-y)\\).

### 4.1 Normal ordering relative to the dressed vacuum

Split

\\[ X_J(x)=C_J(x)+A_J(x) \\]

into dressed creation and annihilation parts. Their scalar commutator satisfies

\\[ [A_J(x),C_J(x)]=2g_JH_MI. \\]

Define the dressed-vacuum normal-ordered series by

\\[ :\operatorname{Exp}\_{\mathrm f}(itX_J(x)):\_P = \operatorname{Exp}\_{\mathrm f}(itC_J(x)) \operatorname{Exp}\_{\mathrm f}(itA_J(x)). \\]

The central-commutator BCH identity, checked coefficientwise, gives

\\[ \boxed{ :\operatorname{Exp}\_{\mathrm f}(itX_J(x)):\_P = \operatorname{Exp}\_{\mathrm f}(g_JH_Mt^2) \operatorname{Exp}\_{\mathrm f}(itX_J(x)). } \tag{22} \\]

Thus normal ordering multiplies each Weyl vertex by the scalar factor \\(\operatorname{Exp}\_{\mathrm f}(g_JH_Mt^2)\\).

If

\\[ \mathcal V_J(t,x) =L^{-1}K_J(x) :\operatorname{Exp}\_{\mathrm f}(itX_J(x)):\_P, \\]

then

\\[ \boxed{ \begin{aligned} &\widehat\omega\_{P,N} (\mathcal V_J(t,x)^\dagger\mathcal V_J(t,y))\\\ &\qquad= \frac{\chi_J(N;x,y)}{L^2} \operatorname{Exp}\_{\mathrm f} \left(2g_JC_M(x-y)t^2\right). \end{aligned} } \tag{23} \\]

The relation between the two correlators is exactly

\\[ \operatorname{Exp}\_{\mathrm f}(2g_JH_Mt^2). \\]

At coincident points, (23) becomes

\\[ L^{-2}\operatorname{Exp}\_{\mathrm f}(2g_JH_Mt^2), \\]

rather than \\(L^{-2}\\).

This difference is mathematical, not merely a choice of notation.

### 4.2 Bare-vacuum normal ordering is different

Equation (6) shows that \\(X_D\\) and \\(X_S\\) are the bare combinations \\(q_R+q_L\\) and \\(q_R-q_L\\). If normal ordering is instead defined relative to \\(\omega_0\\), its scalar factor is

\\[ \operatorname{Exp}\_{\mathrm f}(H_Mt^2), \\]

independent of \\(g_J\\). In the interacting state \\(\omega_P\\), that prescription would produce

\\[ \frac{\chi_J}{L^2} \operatorname{Exp}\_{\mathrm f} \left((2H_M-2g_JD_1(x,y))t^2\right). \tag{24} \\]

Equations (23) and (24) coincide at \\(g_J=1\\), but not generally.

Therefore a proposed normal-ordered correlator is incomplete unless it specifies which vacuum defines normal ordering.

### 4.3 Why this does not establish physical CAR correlators

The formal construction is not yet a physical fermion reconstruction theorem.

A comparison to the actual finite-CAR order parameters requires, at minimum, a concrete operator correspondence between the auxiliary charge–oscillator carrier and the appropriate finite energy-budget sectors, together with a comparison of the states.

The Chapter 14 cyclicity criterion gives a possible route to operator equality, but its hypotheses are substantial: equality on the full ground vector, the appropriate cyclic span, and matching commutator residuals must all be established. A scalar normalization or a two-point contraction is insufficient.

The finite-dimensional CCR obstruction also remains. No nonzero finite-dimensional complex space admits a global pair satisfying \\([A,C]=mI\\) with \\(m\ne0\\), because taking the trace gives \\(0=m\dim V\\).

Furthermore, intermediate projections change products:

\\[ P_tABP_s-P_tAP_mBP_s=P_tA(I-P_m)BP_s. \\]

The right-hand side is generally nonzero. This is precisely why a formal vertex identity on the uncompressed polynomial carrier cannot be transported into \\(B(N,K)\\) by compression alone.

Neither a normal-ordering scalar nor a change of charge gauge repairs this issue.

## 5. Dependency map, minimal theorems, and finite tests

### 5.1 Dependency map

The proof has two independent inputs that meet only in the final tensor-product expectation:

The charge branch fixes the spatial character and source shifts; the oscillator branch fixes the Gaussian exponent. Neither branch requires a finite-CAR representation.

A minimal theorem set, stated in ordinary mathematics, consists of six results:

1\. Dressed-CCR and state theorem. The Bogoliubov substitution is an invertible star automorphism on the uncompressed polynomial CCR algebra, and \\(\omega_0\circ\beta^{-1}\\) is positive with contractions (2).

2\. Charge-word theorem. The signed bilateral shifts are unitary, obey the mixed Klein anticommutation relations, and yield (12) for the specified source phases.

3\. Hermitian-phase theorem. The \\(Q\_\nu\\) and \\(X_J\\) are Hermitian, and the same-channel spatial commutators vanish as in (7).

4\. Finite covariance theorem. The dressed state has centered differences with variance \\(4g_JD_1(x,y)\\).

5\. Algebraic Gaussian theorem. Every centered Hermitian linear oscillator combination satisfies recurrence (16), moments (17), and formal identity (18).

6\. Formal correlator theorem. Combining the preceding results with factor-order preservation gives (1) coefficientwise.

The normal-ordering identity (22) is a separate useful theorem. The finite-CAR comparison is a separate research obligation, not a corollary of these six statements.

### 5.2 Non-vacuity: an interacting four-site example

Take

\\[ L=4,\quad h=2,\quad M=1,\quad \zeta=i, \\]

\\[ c=\frac53,\qquad s=\frac43, \qquad g=\frac19,\qquad g^{-1}=9. \\]

Choose \\(x=0\\), \\(y=1\\), and source charge \\(N=(1,0)\\). Then \\(D_1(0,1)=1\\),

\\[ a_D(N)=-2,\qquad a_S(N)=1. \\]

Equation (1) predicts

\\[ \boxed{ \begin{aligned} C_D(0,1;t) &=-\frac1{16}\operatorname{Exp}\_{\mathrm f} \left(-\frac29t^2\right),\\\ C_S(0,1;t) &=\frac{i}{16}\operatorname{Exp}\_{\mathrm f} \left(-18t^2\right). \end{aligned} } \tag{25} \\]

The SC charge factor is \\(+i\\), whereas the negative exponent in Appendix E.14 would give \\(-i\\). This is an explicit contradiction for the appendix sign, already at order \\(t^0\\).

The example is non-vacuous: \\(s\ne0\\), both channels have nontrivial oscillator coefficients, and their Gaussian strengths differ substantially. It is nevertheless only a test of the auxiliary algebra, not an interacting finite-CAR expectation.

### 5.3 A finite-CAR normalization counterexample

The monograph supplies a complementary four-site free-state test. For a normalized Slater sea with two occupied orbitals per species,

\\[ \langle n\_{R,x}\rangle=\langle n\_{L,x}\rangle=\frac12, \\]

and the distinct-species number expectations factorize. The exact finite-CAR bilinears then satisfy

\\[ \begin{aligned} \langle O\_{\rm CDW}(x)^\dagger O\_{\rm CDW}(x)\rangle &=\langle n\_{L,x}(1-n\_{R,x})\rangle =\frac14,\\\ \langle O\_{\rm SC}(x)^\dagger O\_{\rm SC}(x)\rangle &=\langle n\_{R,x}n\_{L,x}\rangle =\frac14. \end{aligned} \\]

But the Weyl-type formal vertices give \\(L^{-2}=1/16\\) at coincident points.

Thus the supplied normalization and auxiliary correlator cannot be asserted to equal those finite-CAR bilinear expectations universally. The example does not rule out a different, properly renormalized correspondence under additional hypotheses. It rules out the unconditional identification.

## 6. Remaining questions and verified references

The corrected formal target is equation (1), with equation (23) as the distinct dressed-normal-ordered alternative. Both are rigorous algebraic targets once the conventions are fixed; neither is a physical finite-CAR correspondence by itself.

The unresolved mathematical choices are precise:

First, which normal-ordering convention is intended for a later physical vertex? Dressed-vacuum ordering, bare-vacuum ordering, and the Weyl prescription produce different cutoff factors.

Second, which finite-CAR state is to be compared with \\(\omega\_{P,N}\\)? A free sector ground state, a specific interacting Hamiltonian ground state, or a state transported through a restricted current-algebra identification are different problems. For interacting states, the necessary vector or density functional has not been supplied.

Third, what boundary-twist and source-phase convention must the physical correspondence preserve? The integer charge characters are periodic on \\(\mathbb Z/L\mathbb Z\\), but arbitrary species holonomies require additional phase data. An operator identity must match those phases, not merely its oscillator covariance.

The principal literature supports the importance of zero modes, Klein factors, finite-size ordering, and the distinction between constructive bosonization and formal field expressions. It does not automatically establish the newly defined auxiliary construction or its transport to the finite-CAR budget spaces.

Verified primary references are:

- D. C. Mattis and E. H. Lieb, Exact Solution of a Many-Fermion System and Its Associated Boson Field, Journal of Mathematical Physics 6, 304–312 (1965). DOI: [10.1063/1.1704281](https://doi.org/10.1063/1.1704281?utm_source=chatgpt.com).&#x20;

  [image](https://www.google.com/s2/favicons?domain=https://collaborate.princeton.edu\&sz=32)

  Princeton University

- F. D. M. Haldane, 'Luttinger liquid theory' of one-dimensional quantum fluids. I. Properties of the Luttinger model and their extension to the general 1D interacting spinless Fermi gas, Journal of Physics C 14, 2585–2609 (1981). DOI: [10.1088/0022-3719/14/19/010](https://doi.org/10.1088/0022-3719/14/19/010?utm_source=chatgpt.com).&#x20;

  [image](https://www.google.com/s2/favicons?domain=https://collaborate.princeton.edu\&sz=32)

  Princeton University

- Jan von Delft and Herbert Schoeller, Bosonization for Beginners — Refermionization for Experts, Annalen der Physik (1998). DOI: [10.1002/andp.19985100401](https://doi.org/10.1002/andp.19985100401?utm_source=chatgpt.com); arXiv: [cond-mat/9805275](https://arxiv.org/abs/cond-mat/9805275?utm_source=chatgpt.com). Particularly relevant are the sections on Klein factors, vertex operators, and finite-size refermionization.&#x20;

  [image](https://www.google.com/s2/favicons?domain=https://onlinelibrary.wiley.com\&sz=32)

  Wiley Online Library

  +1

- S. Mandelstam, Soliton operators for the quantized sine-Gordon equation, Physical Review D 11, 3026 (1975). DOI: [10.1103/PhysRevD.11.3026](https://doi.org/10.1103/PhysRevD.11.3026?utm_source=chatgpt.com). This concerns fermion reconstruction in its specified continuum model; it is not a proof of the present finite-lattice CAR identification.&#x20;

  [image](https://www.google.com/s2/favicons?domain=https://journals.aps.org\&sz=32)

  Phys. Rev. D



Final assessment. Chapter 20b has a mathematically valid, coefficientwise CDW/SC auxiliary correlator theorem under the prompt's definitions. Its Gaussian exponent, factorials, charge phases, and normalization are consistent. The negative SC phase in Appendix E.14 is a genuine inconsistency, and normal ordering requires an explicit convention and a different prefactor. The strongest justified result is therefore an exact formal charge–oscillator correlation identity, accompanied by a clear separation from physical finite-CAR correlators.
