# Independent mathematical review: Complete ordered Wick theorem for the dressed oscillator state

Project: [Bosonize-Lean](https://github.com/lufreitas0000/bosonize-lean?utm_source=chatgpt.com) Baseline: `40dea8bfbdc849417c072e490480d4f72536116a` Scope: Chapter 19/A08 and the remaining Chapter 20 bridge (CH20b) Review date: October 17, 2026

## 1. Verdict

The existing positive algebraic state supports a complete ordered Wick theorem for arbitrary finite words of linear oscillator forms. No additional physical state, Hilbert-space completion, finite-dimensional squeezed vacuum, or thermodynamic limit is necessary.

The result follows from the dressed vacuum equations, the CCR relations in arbitrary word contexts, and linearity. Positivity establishes that the constructed functional is a legitimate algebraic state and controls Hermitian variances, but it is not the ingredient responsible for Wick factorization.

The precise result is

\\[ \boxed{ \omega_P(Y_1\cdots Y_n)= \begin{cases} \displaystyle \sum\_{\mathcal P\in\operatorname{Pair}(n)} \prod\_{\\{a,b\\}\in\mathcal P,\ a\<b} \omega_P(Y_aY_b), &n\text{ even},\\\\[8pt] 0,&n\text{ odd}. \end{cases} } \\]

Here \\(Y_1,\ldots,Y_n\\) are arbitrary complex homogeneous linear combinations of bare or dressed oscillator generators. Every contraction retains the order inherited from the original word: the generator at position \\(a\\) precedes the generator at position \\(b\\).

For a Hermitian linear form \\(Y\\),

\\[ \boxed{ \omega_P(Y^{2k}) = \frac{(2k)!}{2^k k!} \bigl[\omega_P(Y^2)\bigr]^k, \qquad \omega_P(Y^{2k+1})=0. } \\]

Consequently, in the ring of formal power series,

\\[ \boxed{ \omega_P\\!\left(\operatorname{Exp}\_f(itY)\right) = \operatorname{Exp}\_f\\!\left( -\frac{t^2}{2}\omega_P(Y^2) \right). } \\]

All three formulas are mathematically valid under the specified baseline, including \\(M=0\\), \\(s=0\\), negative values of \\(c\\) or \\(s\\) satisfying the hyperbolic relation, and zero covariance.

### Status classification

| Statement                                                                                     | Assessment                                                                    |
| --------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------- |
| Positive normalized dressed functional, vacuum rules, and contextual CCR descent              | Established baseline; corresponding definitions and theorems inspected in A08 |
| Ordered same-branch and cross-branch two-point contractions                                   | Established CH19 baseline                                                     |
| Complete contraction table, including bare/dressed mixed forms                                | Derived in this answer; not claimed Lean-verified                             |
| General finite ordered-word Wick theorem                                                      | Derived in this answer; not claimed Lean-verified                             |
| Vanishing odd moments and Hermitian even-moment formula                                       | Derived in this answer                                                        |
| Coefficientwise Gaussian formal exponential identity                                          | Derived in this answer; also proposed in manuscript Appendix E                |
| Replacing ordered contractions by symmetrized contractions in an arbitrary fixed word         | Contradicted                                                                  |
| Wick factorization from positivity and two-point data alone                                   | Contradicted                                                                  |
| General finite interacting-CAR correlator equality                                            | Unresolved and not implied                                                    |
| Numeric evaluation at \\(t=1\\), analytic Weyl representation, or continuum vertex power laws | Outside the established result                                                |

Repository distinction. I inspected the A08 and CH19 sources at the supplied commit using the connected GitHub repository. A08 constructs a free-word algebra, its polynomial representation, the positive functional, and CCR descent through arbitrary surrounding words. CH19 establishes particular contractions but not the complete arbitrary-word recursion. The companion audit also explicitly identifies the general Wick theorem as remaining work.

There is one important formalization detail: the existing A08 carrier is a free algebra, not an already constructed CCR quotient. Thus CCR relations should not be asserted as literal identities between elements of that free algebra. They are exact in the polynomial representation and valid inside expectations by contextual relation descent. This distinction is essential for the proof.

The manuscript's Appendix E.5 already sketches the Gaussian moment recurrence. Its mathematical claim is justified by the argument below, but the manuscript proposal should not be confused with an accepted Lean theorem.&#x20;

main.pdf



## 2. Mathematical objects, domains, and conventions

### 2.1 Oscillator carrier

Let

\\[ I_M=\\{R,L\\}\times\\{1,\ldots,M\\}, \qquad M\in\mathbb N_0. \\]

For \\(j=(\nu,m)\\), write \\(\mu_j=m>0\\). The concrete polynomial carrier is

\\[ \mathscr P_M=\mathbb C[X_j:j\in I_M], \\]

with finite-degree polynomials but no maximum degree.

The operators are

\\[ C_j f=X_jf,\qquad A_jf=\mu_j\frac{\partial f}{\partial X_j}. \\]

They obey

\\[ [A_j,C_k]=\mu_j\delta\_{jk}I,\qquad [A_j,A_k]=[C_j,C_k]=0. \\]

The polynomial inner product is

\\[ \langle X^\alpha,X^\beta\rangle = \delta\_{\alpha\beta} \prod\_{j\in I_M}\alpha_j!\\,\mu_j^{\alpha_j}, \\]

conjugate-linear in its first entry. Consequently \\(A_j^\ast=C_j\\) on the common polynomial domain.

The normalized vacuum functional is

\\[ \omega_0(a)=\langle1,\pi_0(a)1\rangle. \\]

It satisfies, for every finite polynomial word \\(a\\),

\\[ \omega_0(aA_j)=0,\qquad \omega_0(C_ja)=0. \\]

The vacuum is centered:

\\[ \omega_0(A_j)=\omega_0(C_j)=0. \\]

### 2.2 Bogoliubov substitution

Let \\(\bar R=L\\), \\(\bar L=R\\), and assume

\\[ c,s\in\mathbb R,\qquad c^2-s^2=1. \\]

Define dressed generators

\\[ D\_{\nu m}:=\beta(A\_{\nu m}) =cA\_{\nu m}+sC\_{\bar\nu m}, \\]

\\[ E\_{\nu m}:=\beta(C\_{\nu m}) =cC\_{\nu m}+sA\_{\bar\nu m}. \\]

The inverse relations are

\\[ \boxed{ A\_{\nu m}=cD\_{\nu m}-sE\_{\bar\nu m}, \qquad C\_{\nu m}=cE\_{\nu m}-sD\_{\bar\nu m}. } \\]

The dressed functional is

\\[ \omega_P=\omega_0\circ\beta^{-1}. \\]

Its defining vacuum conditions are

\\[ \omega_P(aD_j)=0, \qquad \omega_P(E_ja)=0, \\]

for arbitrary finite words \\(a\\).

Crucially, these are left-creator and right-annihilator rules, not interchangeable statements.

On the represented CCR algebra, or within arbitrary word expectations after relation descent,

\\[ [D_j,E_k]=\mu_j\delta\_{jk}I,\qquad [D_j,D_k]=[E_j,E_k]=0. \\]

No choice of signs for \\(c,s\\) beyond \\(c^2-s^2=1\\) is needed.

The spatial lattice length \\(L=2h\\), finite-CAR charge budgets, and margin hypotheses play no role in these purely algebraic oscillator identities. In particular, the Wick theorem does not require an identification between \\(\mathscr P_M\\) and \\(B(N,K)\\).

## 3. Complete ordered contraction table

### 3.1 General contraction formula

Every homogeneous linear oscillator form \\(Y\\), whether written in bare or dressed generators, has a unique decomposition

\\[ Y=Y^-+Y^+, \\]

where

\\[ Y^-=\sum\_{j\in I_M}u_jD_j, \qquad Y^+=\sum\_{j\in I_M}v_jE_j. \\]

The coefficients \\(u_j,v_j\in\mathbb C\\) are arbitrary.

The vacuum rules immediately imply

\\[ \omega_P(Y)=0, \\]

and

\\[ \begin{aligned} \omega_P(Y_iY_j) &=\omega_P(Y_i^-Y_j^+)\\\ &=\sum\_{r\in I_M}\mu_r u\_{ir}v\_{jr}. \end{aligned} \\]

Thus the universal contraction is

\\[ \boxed{ Q\_{ij}:=\omega_P(Y_iY_j) =\sum\_{\nu,m}m\\,u\_{i,\nu m}v\_{j,\nu m}. } \tag{3.1} \\]

This is complex bilinear, not sesquilinear. Complex conjugation appears only when Hermiticity imposes a relation between creation and annihilation coefficients.

Reversal gives

\\[ Q\_{ij}-Q\_{ji} = \omega_P([Y_i,Y_j]) = [Y_i,Y_j], \\]

where the final commutator is a scalar multiple of the identity in the CCR representation.

Consequently, \\(Q\_{ij}\\) need not be symmetric.

For forms originally expressed using only bare generators,

\\[ Y_i=\sum\_{\nu,m} \left( a\_{i,\nu m}A\_{\nu m} +b\_{i,\nu m}C\_{\nu m} \right), \\]

the dressed coefficients are

\\[ \boxed{ \begin{aligned} u\_{i,\nu m}&=ca\_{i,\nu m}-sb\_{i,\bar\nu m},\\\ v\_{i,\nu m}&=cb\_{i,\nu m}-sa\_{i,\bar\nu m}. \end{aligned} } \tag{3.2} \\]

If dressed generators are also explicitly present, their coefficients are simply added to the corresponding \\(u\\) and \\(v\\).

Equation (3.1) therefore handles arbitrary mixtures of bare and dressed forms without a separate case analysis.

### 3.2 The complete generator table

For any \\(m,n\in\\{1,\ldots,M\\}\\), define

\\[ \delta=\delta\_{\nu\eta}, \qquad \kappa=\delta\_{\eta,\bar\nu}. \\]

Every entry in the following table is multiplied by \\(m\delta\_{mn}\\). The row generator is the left factor, and the column generator is the right factor.

| \\(\omega_P(\text{row}\_{\nu m}\\,\text{column}\_{\eta n})/(m\delta\_{mn})\\) | \\(A\_\eta\\)   | \\(C\_\eta\\)   | \\(D\_\eta\\) | \\(E\_\eta\\)  |
| ----------------------------------------------------------------------------- | --------------- | --------------- | ------------- | -------------- |
| \\(A\_\nu\\)                                                                  | \\(-cs\kappa\\) | \\(c^2\delta\\) | \\(0\\)       | \\(c\delta\\)  |
| \\(C\_\nu\\)                                                                  | \\(s^2\delta\\) | \\(-cs\kappa\\) | \\(0\\)       | \\(-s\kappa\\) |
| \\(D\_\nu\\)                                                                  | \\(-s\kappa\\)  | \\(c\delta\\)   | \\(0\\)       | \\(\delta\\)   |
| \\(E\_\nu\\)                                                                  | \\(0\\)         | \\(0\\)         | \\(0\\)       | \\(0\\)        |

The table is shorthand for the exact formulas, and the common factor should not be interpreted as a division when \\(\delta\_{mn}=0\\).

It includes all reversed orders, both branch orientations, same-branch and cross-branch correlations, and bare/dressed mixed contractions.

In particular, for bare generators,

\\[ \boxed{ \begin{aligned} \omega_P(A\_{\nu m}C\_{\eta n}) &=mc^2\delta\_{mn}\delta\_{\nu\eta},\\\ \omega_P(C\_{\nu m}A\_{\eta n}) &=ms^2\delta\_{mn}\delta\_{\nu\eta},\\\ \omega_P(A\_{\nu m}A\_{\eta n}) &=-mcs\\,\delta\_{mn}\delta\_{\eta,\bar\nu},\\\ \omega_P(C\_{\nu m}C\_{\eta n}) &=-mcs\\,\delta\_{mn}\delta\_{\eta,\bar\nu}. \end{aligned} } \tag{3.3} \\]

These agree with Chapter 19, Theorem 19.9, including the anomalous cross-branch sign.&#x20;

main.pdf



For dressed generators,

\\[ \boxed{ \omega_P(D\_{\nu m}E\_{\eta n}) =m\delta\_{mn}\delta\_{\nu\eta}, } \\]

and the other three dressed pair types vanish.

A useful independent check is

\\[ \omega_P(A\_{\nu m}C\_{\nu m}) - \omega_P(C\_{\nu m}A\_{\nu m}) =m(c^2-s^2)=m. \\]

This reproduces the CCR normalization for either sign of \\(c\\) or \\(s\\).

Another check comes from a mixed contraction:

\\[ \begin{aligned} \omega_P(D\_{Rm}A\_{Lm}) &=\omega_P\bigl(D\_{Rm}(cD\_{Lm}-sE\_{Rm})\bigr)\\\ &=-ms. \end{aligned} \\]

Reversing the factors gives zero:

\\[ \omega_P(A\_{Lm}D\_{Rm})=0. \\]

Thus order dependence persists even when one generator is bare and the other dressed.

All contractions vanish between different positive mode numbers. The only nonzero cross-branch contractions occur at equal mode number and with the orientations specified by the table.

For more than one independent right/left species pair, the same result extends blockwise, provided the Bogoliubov transformation pairs those species and preserves their CCR. Such an extension should not be silently identified with the present two-orientation A08 carrier.

## 4. Derivation of the ordered Wick theorem

### 4.1 The fundamental pull-through identity

Let \\(Y_1,\ldots,Y_n\\) be arbitrary homogeneous linear oscillator forms, with \\(n\geq2\\).

Write

\\[ Y_1=Y_1^-+Y_1^+. \\]

Because a dressed creator on the left has vanishing expectation,

\\[ \omega_P(Y_1Y_2\cdots Y_n) = \omega_P(Y_1^-Y_2\cdots Y_n). \\]

For every \\(j\\),

\\[ [Y_1^-,Y_j] = \sum_r\mu_r u\_{1r}v\_{jr}\\,I = Q\_{1j}I. \\]

This is a contextual CCR identity: in the existing free-word formulation, it is used inside expectations via relation descent, rather than asserted as an equality of free-algebra elements.

Move \\(Y_1^-\\) successively to the right:

\\[ \begin{aligned} \omega_P(Y_1^-Y_2\cdots Y_n) ={}&Q\_{12}\\,\omega_P(Y_3\cdots Y_n)\\\ &+\omega_P(Y_2Y_1^-Y_3\cdots Y_n). \end{aligned} \\]

Applying the same relation again,

\\[ \begin{aligned} \omega_P(Y_2Y_1^-Y_3\cdots Y_n) ={}&Q\_{13}\\,\omega_P(Y_2Y_4\cdots Y_n)\\\ &+\omega_P(Y_2Y_3Y_1^-\cdots Y_n). \end{aligned} \\]

Continuing produces

\\[ \begin{aligned} \omega_P(Y_1\cdots Y_n) ={}&\sum\_{j=2}^n Q\_{1j}\\, \omega_P(Y_2\cdots\widehat{Y_j}\cdots Y_n)\\\ &+\omega_P(Y_2\cdots Y_nY_1^-). \end{aligned} \\]

The final term vanishes because the dressed annihilator is now at the right boundary.

Therefore,

\\[ \boxed{ \omega_P(Y_1\cdots Y_n) = \sum\_{j=2}^n Q\_{1j}\\, \omega_P(Y_2\cdots\widehat{Y_j}\cdots Y_n). } \tag{4.1} \\]

The hat means that precisely that factor is omitted; all other factors retain their original relative order.

This is the central theorem. No permutation of the remaining word is allowed.

### 4.2 Termination and induction

The elementary cases are

\\[ \omega_P(1)=1,\qquad \omega_P(Y_1)=0. \\]

For \\(n\geq2\\), equation (4.1) reduces a moment of length \\(n\\) to moments of length \\(n-2\\).

The calculation terminates for two reasons: the pull-through moves the distinguished annihilator one position right at each step, and the recursive call strictly reduces word length.

Define \\(\operatorname{Pair}(n)\\) as the collection of perfect matchings of \\(\\{1,\ldots,n\\}\\).

For even \\(n\\), partition all pairings according to the unique index \\(j>1\\) matched with index \\(1\\).

For each such \\(j\\), the remaining indices admit precisely the pairings of the shortened word in equation (4.1). Applying the induction hypothesis gives

\\[ \boxed{ \omega_P(Y_1\cdots Y\_{2k}) = \sum\_{\mathcal P\in\operatorname{Pair}(2k)} \prod\_{\\{a,b\\}\in\mathcal P,\ a\<b} Q\_{ab}. } \tag{4.2} \\]

There are \\((2k-1)!!\\) pairings. Since every contraction is scalar, the individual scalar factors commute. That does not permit reversing the two operators within a contraction.

For odd \\(n\\), every recursion terminates at a one-point moment, which vanishes. Hence

\\[ \boxed{\omega_P(Y_1\cdots Y\_{2k+1})=0.} \tag{4.3} \\]

No separate parity operator is needed.

### 4.3 Hermitian even moments

Set \\(Y_1=\cdots=Y_n=Y\\). Every ordered two-point contraction is now the same scalar,

\\[ q=\omega_P(Y^2). \\]

Equation (4.1) becomes

\\[ \omega_P(Y^n) = (n-1)q\\,\omega_P(Y^{n-2}). \\]

The initial values are \\(1\\) and \\(0\\), so

\\[ \omega_P(Y^{2k})=(2k-1)!!q^k = \frac{(2k)!}{2^k k!}q^k. \\]

In fact, this algebraic moment formula is true even when \\(Y\\) is not Hermitian. Hermiticity matters for interpreting \\(q\\) as a nonnegative variance.

For \\(Y=Y^\ast\\), its dressed coefficients satisfy

\\[ v_j=\overline{u_j}. \\]

Consequently,

\\[ \boxed{ q=\omega_P(Y^2) =\sum\_{j\in I_M}\mu_j|u_j|^2\geq0. } \tag{4.4} \\]

This agrees with state positivity, because \\(Y^2=Y^\ast Y\\).

There is a useful stronger fact:

\\[ \boxed{ Y=Y^\ast,\quad \omega_P(Y^2)=0 \quad\Longrightarrow\quad Y=0 } \\]

within the homogeneous linear oscillator space.

Indeed, all \\(\mu_j>0\\), so (4.4) forces every \\(u_j=0\\). Hermiticity forces \\(v_j=0\\), and the invertibility of the Bogoliubov substitution then gives \\(Y=0\\).

For \\(M=0\\), this statement is vacuous because there are no nonzero homogeneous linear oscillator forms.

It would be incorrect to make the same inference for a non-Hermitian form: for example,

\\[ \omega_0(A_m^2)=0 \\]

although \\(A_m\neq0\\).

### 4.4 Formal Gaussian identity

Let \\(t\\) be central, with \\(t^\ast=t\\), and define

\\[ \operatorname{Exp}\_f(itY) = \sum\_{n=0}^{\infty}\frac{i^nt^nY^n}{n!}. \\]

Extend \\(\omega_P\\) coefficientwise to the formal series ring.

Using the moment theorem,

\\[ \begin{aligned} \omega_P(\operatorname{Exp}\_f(itY)) &= \sum\_{k=0}^{\infty} \frac{(-1)^kt^{2k}}{(2k)!} \frac{(2k)!}{2^kk!}q^k\\\ &= \sum\_{k=0}^{\infty} \frac{1}{k!} \left(-\frac{qt^2}{2}\right)^k. \end{aligned} \\]

Therefore,

\\[ \boxed{ \omega_P(\operatorname{Exp}\_f(itY)) = \operatorname{Exp}\_f(-qt^2/2). } \tag{4.5} \\]

At coefficient \\(t^{2k}\\), the right side is exactly

\\[ \frac{(-1)^kq^k}{2^kk!}, \\]

and every odd coefficient is zero.

Each coefficient requires finitely many multiplications and contractions. There is no infinite sum being evaluated numerically.

The coefficientwise extension should not itself be called a complex-valued positive state on the formal-series algebra. No order structure on arbitrary complex formal series has been introduced.

### 4.5 Stronger ordered multivariate identity

The same argument gives a useful result for products of formal exponentials.

For fixed \\(Y_1,\ldots,Y_r\\) and independent commuting formal variables \\(t_1,\ldots,t_r\\),

\\[ \boxed{ \begin{aligned} &\omega_P\left( \operatorname{Exp}\_f(it_1Y_1)\cdots \operatorname{Exp}\_f(it_rY_r) \right)\\\ &\qquad= \operatorname{Exp}\_f\left( -\frac12\sum\_{i=1}^{r}t_i^2Q\_{ii} -\sum\_{i\<j}t_it_jQ\_{ij} \right). \end{aligned} } \tag{4.6} \\]

The order of the exponential factors is fixed. Between different factors, the exponent uses \\(Q\_{ij}=\omega_P(Y_iY_j)\\) in that order, not \\(Q\_{ji}\\).

This follows coefficientwise by expanding each exponential and applying (4.2). Conversely, differentiating the formal identity with respect to the independent central variables recovers the entire ordered-word theorem.

Equation (4.6) is useful for future formal vertex correlators, but it does not establish any microscopic finite-CAR vertex identity.

## 5. Symmetrization, a fourth-moment test, and counterexamples

### 5.1 When a symmetrized Wick theorem is valid

Define the symmetrized covariance

\\[ S\_{ij} = \frac12\omega_P(Y_iY_j+Y_jY_i) = \frac12(Q\_{ij}+Q\_{ji}). \\]

There are two distinct mathematical statements.

For an ordered product, the Wick theorem uses \\(Q\_{ij}\\), and replacing it by \\(S\_{ij}\\) is generally false.

For the fully symmetrized operator product

\\[ \operatorname{Sym}(Y_1\cdots Y_n) = \frac1{n!}\sum\_{\sigma\in S_n} Y\_{\sigma(1)}\cdots Y\_{\sigma(n)}, \\]

one has

\\[ \boxed{ \omega_P(\operatorname{Sym}(Y_1\cdots Y\_{2k})) = \sum\_{\mathcal P\in\operatorname{Pair}(2k)} \prod\_{\\{a,b\\}\in\mathcal P}S\_{ab}. } \tag{5.1} \\]

Odd symmetrized moments vanish.

To prove this, apply the one-form moment theorem to

\\[ Z=\sum_i t_iY_i \\]

with commuting indeterminates \\(t_i\\). Its quadratic moment is

\\[ \omega_P(Z^2)=\sum\_{i,j}t_it_jS\_{ij}. \\]

Comparing the coefficient of \\(t_1\cdots t_n\\) in the resulting formal Gaussian identity establishes (5.1).

This works even when the \\(Y_i\\) do not commute. The operator product itself has been symmetrized.

If all \\(Y_i\\) commute pairwise, then

\\[ Q\_{ij}=Q\_{ji}=S\_{ij}, \\]

so the ordered and symmetrized theorems agree.

For general noncommuting forms, they are different statements.

### 5.2 A mixed-orientation fourth moment

Fix one mode \\(m\geq1\\) and consider

\\[ W=A\_{Rm}C\_{Rm}A\_{Lm}C\_{Lm}. \\]

There are three possible pairings:

\\[ \begin{aligned} \omega_P(W) ={}& \omega_P(A_RC_R)\omega_P(A_LC_L)\\\ &+\omega_P(A_RA_L)\omega_P(C_RC_L)\\\ &+\omega_P(A_RC_L)\omega_P(C_RA_L). \end{aligned} \\]

The mode index \\(m\\) is suppressed only within this calculation.

Using the complete table,

\\[ \begin{aligned} \omega_P(A_RC_R)&=mc^2,\\\ \omega_P(A_LC_L)&=mc^2,\\\ \omega_P(A_RA_L)&=-mcs,\\\ \omega_P(C_RC_L)&=-mcs, \end{aligned} \\]

while the last pairing vanishes.

Thus

\\[ \boxed{ \omega_P(A_RC_RA_LC_L) =m^2(c^4+c^2s^2) =m^2c^2(c^2+s^2). } \tag{5.2} \\]

This example simultaneously tests the ordered \\(AC\\) contractions, the anomalous \\(AA\\) and \\(CC\\) contractions, and the relative sign of the Bogoliubov transformation.

At \\(s=0\\), it reduces to \\(m^2\\), as required by two independent bare vacuum contractions.

### 5.3 Counterexample to unordered contractions

Consider a single oscillator with \\(m=1\\), \\(c=1\\), \\(s=0\\), and

\\[ [A,C]=1,\qquad A1=0. \\]

The exact expectation is

\\[ \omega_0(ACAC)=1. \\]

Indeed, applying operators from the right gives

\\[ ACAC\\,1=1. \\]

The ordered Wick expansion is

\\[ \begin{aligned} \omega_0(ACAC) ={}&\omega_0(AC)\omega_0(AC)\\\ &+\omega_0(AA)\omega_0(CC)\\\ &+\omega_0(AC)\omega_0(CA)\\\ ={}&1+0+0=1. \end{aligned} \\]

An unordered rule that identifies \\(CA\\) with \\(AC\\) incorrectly gives \\(2\\).

Replacing every ordered contraction by its symmetrized value also fails. Since

\\[ S(A,C)=\frac12, \\]

that incorrect substitution would give \\(1/2\\).

The three numbers describe different operations:

\\[ \begin{aligned} \omega_0(ACAC)&=1,\\\ \text{incorrect unordered pairing value}&=2,\\\ \omega_0(\operatorname{Sym}(ACAC))&=\frac12. \end{aligned} \\]

This is already a counterexample in the free vacuum, so interactions or anomalous contractions are not responsible for the problem.

### 5.4 Why positivity and two-point functions alone are insufficient

Consider the unit-weight oscillator and normalized number states \\(|n\rangle\\). Let \\(Q=A+C\\).

The number-state formulas give

\\[ \langle n|Q^2|n\rangle=2n+1, \\]

and

\\[ \langle n|Q^4|n\rangle=6n^2+6n+3. \\]

Take the positive normalized states

\\[ \varphi_1(a)=\langle1|a|1\rangle \\]

and

\\[ \varphi_2(a) =\frac12\langle0|a|0\rangle +\frac12\langle2|a|2\rangle. \\]

Both have the same complete one- and two-point data:

\\[ \varphi_i(A)=\varphi_i(C)=0, \\]

\\[ \varphi_i(CA)=1,\quad \varphi_i(AC)=2,\quad \varphi_i(AA)=\varphi_i(CC)=0. \\]

In particular,

\\[ \varphi_1(Q^2)=\varphi_2(Q^2)=3. \\]

But

\\[ \varphi_1(Q^4)=15, \qquad \varphi_2(Q^4)=21. \\]

A Gaussian Wick rule would predict

\\[ 3\varphi_i(Q^2)^2=27. \\]

Neither state satisfies that prediction.

Therefore, normalized positivity, CCR relations and even the complete two-point contraction table do not characterize a Gaussian state.

The additional decisive hypothesis is the annihilation/creation vacuum structure used in the pull-through identity. Neither \\(\varphi_1\\) nor \\(\varphi_2\\) satisfies the relevant oscillator vacuum equations.

This is why the existing A08 state is sufficient, whereas an arbitrary positive functional with CH19-like two-point data would not be.

## 6. Dependencies and minimal theorem family

The mathematically economical proof should follow the dependency structure below.

Polynomial oscillator representation

Weighted monomial pairing, algebraic adjoints, exact CCR

Free-word vacuum and contextual CCR descent

Normalization, boundary annihilation rules, word-context substitution

Bogoliubov transformation and pullback state

Inverse transformation, dressed vacuum, positivity

Universal ordered contraction and pull-through recurrence

Equations (3.1) and (4.1)

General Wick moments

Ordered pairings and odd-moment vanishing

Formal Gaussian identities

One-form and ordered multivariate series

### Minimal mathematical theorem list

1\. Vacuum normalization and boundary annihilation. Establish \\(\omega_P(1)=1\\), \\(\omega_P(aD_j)=0\\), and \\(\omega_P(E_ja)=0\\) for every finite word \\(a\\).

2\. Contextual dressed CCR. Establish the three dressed commutation relations inside arbitrary prefix/suffix expectations. This is the appropriate statement on the current free-algebra carrier.

3\. Universal ordered contraction. Establish equation (3.1), followed by the generator contraction table in Section 3.2.

4\. Linear pull-through recurrence. Establish equation (4.1) for arbitrary finite words of homogeneous linear forms. This is the only essential new structural lemma.

5\. Ordered Wick factorization. Prove equations (4.2) and (4.3) by induction on word length.

6\. Gaussian consequences. Derive the single-form moment formula, coefficientwise formal exponential identities, symmetrized-product theorem, and covariance positivity.

This family is sufficient for the requested mathematical result. A general normal-ordering rewrite system, construction of a completed Weyl algebra, or tensor-product representation of every oscillator mode is unnecessary.

The strongest abstraction is the pull-through recurrence, not a collection of increasingly complicated explicit four-, six-, or eight-point calculations.

### Which hypotheses are used where?

| Input                                 | Mathematical role                                                         |
| ------------------------------------- | ------------------------------------------------------------------------- |
| Complex linearity                     | Expanding forms and collecting contractions                               |
| Normalization                         | Empty-word base case and scalar commutator contributions                  |
| Left dressed-creator vacuum rule      | Removing the leftmost creation component                                  |
| Right dressed-annihilator vacuum rule | Killing the terminal term of pull-through                                 |
| CCR contextual descent                | Commuting an annihilator across arbitrary intervening words               |
| Bogoliubov inverse                    | Converting bare coefficients to dressed coefficients                      |
| Positivity                            | Establishing legitimacy of the state and nonnegative Hermitian covariance |
| Algebraic adjoints                    | Relating Hermitian creation/annihilation coefficients                     |
| Finite mode count                     | Ensuring each linear form and each coefficient computation is finite      |

Importantly, positivity does not appear in the derivation of equation (4.1). The same recurrence can characterize Gaussian moments for a nonpositive normalized linear functional if both vacuum boundary conditions and the contextual CCR are assumed.

Conversely, positivity plus only the right-annihilator equation suffices to recover the left-creator equation when the star operation and adjoint relation are properly established. The two-sided formulation is nevertheless clearer and is already available here.

## 7. Finite non-vacuity test and limiting cases

Take \\(M=1\\), with two orientations \\(R,L\\), and choose

\\[ m=1,\qquad c=\frac53,\qquad s=\frac43. \\]

The hyperbolic identity holds exactly:

\\[ c^2-s^2=\frac{25}{9}-\frac{16}{9}=1. \\]

Define the Hermitian form

\\[ Y=A_R+C_R+A_L+C_L. \\]

From the Bogoliubov inverse,

\\[ \beta^{-1}(Y)=(c-s)Y=\frac13Y. \\]

The bare vacuum has variance

\\[ \omega_0(Y^2)=2. \\]

Hence

\\[ \boxed{ \omega_P(Y^2)=\frac29, \qquad \omega_P(Y^4)=3\left(\frac29\right)^2 =\frac4{27}. } \\]

The coefficientwise formal identity is therefore

\\[ \omega_P(\operatorname{Exp}\_f(itY)) = \operatorname{Exp}\_f\left(-\frac{t^2}{9}\right). \\]

Its first terms are

\\[ 1-\frac{t^2}{9} +\frac{t^4}{162} -\frac{t^6}{4374}+\cdots . \\]

These are rational identities in the formal series ring. No numerical approximation or convergence assumption is involved.

This test is nontrivial because \\(s\neq0\\) and the state contains anomalous cross-branch contractions. Nevertheless, the Hermitian variance remains strictly positive and the fourth moment satisfies the Gaussian theorem.

The boundary cases are summarized here:

| Case                             | Outcome                                                                |
| -------------------------------- | ---------------------------------------------------------------------- |
| \\(M=0\\)                        | No oscillator generators; all homogeneous linear forms are zero        |
| \\(Y=0\\)                        | All positive-degree moments vanish; formal expectation equals \\(1\\)  |
| \\(Y=Y^\ast\\), \\(q=0\\)        | \\(Y=0\\), by strict positivity on the linear oscillator space         |
| Non-Hermitian \\(Y\\), \\(q=0\\) | Gaussian moment formula holds; \\(Y\\) need not vanish                 |
| \\(s=0\\)                        | Ordinary bare vacuum, with \\(c=\pm1\\)                                |
| \\(s<0\\)                        | All formulas hold; anomalous contractions change sign accordingly      |
| \\(c<0\\)                        | All formulas hold; no convention \\(c>0\\) is mathematically necessary |
| Arbitrary finite \\(M\\)         | Valid without relating \\(M\\) to the lattice half-size \\(h\\)        |

The uncompressed oscillator non-vacuity test does not imply that the corresponding three-dimensional compressed oscillator pair has a common vacuum. Indeed, A08's finite compressed counterexample rules that out when \\(s\neq0\\) for its specified compression.

There is no contradiction: the tested Gaussian state lives on the unrestricted polynomial oscillator algebra, not on that compressed finite-dimensional carrier.

## 8. Remaining questions and implications for CH20b

### 8.1 What has been resolved?

The mathematical obstruction to a complete ordered Wick theorem is absent in the existing A08 setting.

The state is not merely positive with a selected collection of two-point functions. It has the stronger defining structure of a dressed algebraic vacuum, and that structure yields all moments by a terminating recurrence.

Thus the missing general word/moment theorem is a proof obligation, not a missing physical hypothesis.

This result also clarifies that the Gaussian recurrence in manuscript Appendix E.5 is valid for a Hermitian oscillator-linear field difference, provided that field difference belongs to this oscillator space and is evaluated in the constructed state.

### 8.2 What remains unresolved?

The following are logically independent of the general Wick theorem.

Formal charge and vertex factors. The charge-shift algebra must be specified separately. A formal oscillator Gaussian identity does not establish an arbitrary charge-sector correlation or justify rearranging charge words through oscillator exponentials.

Microscopic field reconstruction. The theorem does not give the full ground-vector equality or common commutator residuals required by the conditional Chapter 14 criterion. Consequently, it does not prove that a projected microscopic fermion equals a proposed polynomial vertex.

Interacting finite-CAR ground states. Nothing here identifies \\(\omega_P\\) with the state of an interacting finite-band fermionic Hamiltonian. The positive oscillator functional and an interacting finite-CAR density matrix are different mathematical objects.

Finite compressions. Projection does not preserve products. A Wick identity involving uncompressed words cannot be transported by substituting compressed operators without analyzing the discarded intermediate sectors and their excursion margins.

Analytic exponentials. The formal identities do not evaluate the series at a numerical parameter. Such evaluation requires additional analytic representation and domain arguments.

These distinctions preserve the original scope of version 1 without relying on the deferred version 2 architecture.

### 8.3 Clarifications that would affect a later extension

The present theorem needs no further assumptions. Three definitions would, however, matter for extending it beyond this question.

First, if the intended oscillator index includes multiple physical flavors rather than only the existing \\(R,L\\) orientation pair, the precise species-pairing involution and its commutator weights should be specified.

Second, a future theorem about general affine forms \\(Y_i+\lambda_iI\\) should explicitly include nonzero means. The centered pairing formula is stated here for homogeneous linear forms.

Third, if CH20b intends a general theorem about products containing both charge-shift operators and oscillator-linear forms, their commutation relations and the state on the combined algebra must be specified. The oscillator theorem alone does not determine those mixed moments.

None of these questions prevents the complete oscillator Wick theorem established mathematically above.

## 9. Verified references

The proof above is self-contained. The following references provide the historical Wick theorem and established mathematical treatments of quasifree CCR states. Their bibliographic identifiers were checked against publisher or journal records.

G. C. Wick (1950). “The Evaluation of the Collision Matrix.” Physical Review 80, 268–272. DOI: [10.1103/PhysRev.80.268](https://doi.org/10.1103/PhysRev.80.268?utm_source=chatgpt.com). This is the original Wick theorem reference; the particular polynomial-vacuum recurrence here is proved directly rather than imported from its field-theoretic formulation.&#x20;

[image](https://www.google.com/s2/favicons?domain=https://journals.aps.org\&sz=32)

Phys. Rev.



Huzihiro Araki and Masafumi Shiraishi (1971). “On Quasifree States of the Canonical Commutation Relations (I).” Publications of the Research Institute for Mathematical Sciences 7(1), 105–120. DOI: [10.2977/PRIMS/1195193785](https://doi.org/10.2977/PRIMS/1195193785?utm_source=chatgpt.com). This provides a general CCR quasifree-state framework, substantially broader than the finite-generator algebraic calculation needed here.&#x20;

[image](https://www.google.com/s2/favicons?domain=https://ems.press\&sz=32)

EMS Press



H. Araki and E. J. Woods (1963). “Representations of the Canonical Commutation Relations Describing a Nonrelativistic Infinite Free Bose Gas.” Journal of Mathematical Physics 4(5), 637–662. DOI: [10.1063/1.1704002](https://doi.org/10.1063/1.1704002?utm_source=chatgpt.com). Relevant for the distinction between algebraic CCR representations and state representations, although its infinite-system analysis is not needed for this theorem.&#x20;

[image](https://www.google.com/s2/favicons?domain=https://cir.nii.ac.jp\&sz=32)

CiNii Research



Repository sources examined: [A08OscillatorStates.lean](https://github.com/lufreitas0000/bosonize-lean/blob/40dea8bfbdc849417c072e490480d4f72536116a/Bosonize/Core/A08OscillatorStates.lean?utm_source=chatgpt.com), [Ch19Correlations.lean](https://github.com/lufreitas0000/bosonize-lean/blob/40dea8bfbdc849417c072e490480d4f72536116a/Bosonize/Core/Ch19Correlations.lean?utm_source=chatgpt.com), and the accompanying Chapter 19/A08 audit notes at the same commit.

## Final assessment

The strongest justified target for Bosonize-Lean version 1 is:

\\[ \boxed{ \begin{gathered} \text{Normalized dressed algebraic vacuum}\\\ +\ \text{contextual CCR}\\\ +\ \text{two vacuum boundary rules}\\\\[3pt] \Longrightarrow\\\\[3pt] \text{complete ordered Wick factorization}\\\ \Longrightarrow\\\ \text{exact coefficientwise Gaussian identities}. \end{gathered} } \\]

This is stronger than establishing isolated higher-order contractions and narrower than claiming Gaussianity of a microscopic interacting fermionic ground state.

The principal technical recommendation is to formulate the mathematical theorem around the universal contraction and terminating pull-through recurrence, with arbitrary finite words and preserved factor order. The existing positive state supplies all the hypotheses needed for that theorem. No new state construction or physical identification is required.

Status: mathematically derived in this review, compatible with the inspected baseline, but not claimed to have been formalized or checked in Lean.
