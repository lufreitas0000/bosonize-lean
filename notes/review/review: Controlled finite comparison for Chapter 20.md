# Independent mathematical review: Controlled finite comparison for Chapter 20

Project: [Bosonize-Lean](https://github.com/lufreitas0000/bosonize-lean?utm_source=chatgpt.com) Reference commit: `40dea8bfbdc849417c072e490480d4f72536116a` Scope: Finite lattice, finite CAR, algebraic oscillator states, and the unresolved Chapter 20 bridge (CH20b).

## 1. Verdict

Chapter 20 can have a mathematically meaningful version-1 closure without proving a global finite CAR–CCR field identity or identifying the interacting fermionic ground state with the abstract Bogoliubov vacuum.

I recommend two complementary results:

1. An exact finite-degree current-moment comparison, using the existing Haldane partition correspondence and actual CAR density operators, with explicit total-energy margins. This compares genuine finite-CAR matrix elements with the algebraic oscillator functional, including Bogoliubov dressing, but does not identify the interacting physical state.
2. A quantitative physical field and order-parameter comparison, keeping the actual CAR operators unchanged, with separately measurable field-dictionary defects, intermediate-projection residuals, mode-truncation defects, and state differences.

The first provides a positive exact theorem. The second makes the unresolved physical bridge falsifiable without assuming that its error vanishes.

### Classification of conclusions

| Statement                                                                     | Status                                                                               |
| ----------------------------------------------------------------------------- | ------------------------------------------------------------------------------------ |
| Finite-dimensional global CCR representation with \\([A,C]=mI\\), \\(m\ne0\\) | Contradicted, by trace                                                               |
| Universal cancellation of \\(P_tA(1-P_m)BP_s\\)                               | Contradicted, by an explicit finite-CAR witness                                      |
| Exact low-degree current moments under sufficiently strong margins            | Derivable conditionally from the accepted current-action and partition-basis results |
| Exact equality of finite interacting ground-state moments with \\(\omega_P\\) | Unresolved                                                                           |
| Equality of physical fermion fields with Chapter 14's polynomial candidate    | Unresolved; requires the physical CH14 obligations                                   |
| A finite operator-norm bound incorporating residuals and dictionary defects   | Proved below, as a general finite-dimensional inequality                             |
| Equality of the formal Chapter 20 vertices with physical CDW/SC bilinears     | False without additional normalization and operator/state identification             |
| Analytic evaluation of formal vertices at \\(t=1\\)                           | Not justified and unnecessary for finite version 1                                   |

The repository at the specified commit contains the finite constructions in `Ch13KleinFactors.lean`, `Ch14Mandelstam.lean`, `Ch19Correlations.lean`, `Ch20CDW.lean`, and `A08OscillatorStates.lean`. I checked the relevant repository definitions through the connected GitHub source. The mathematical statements derived below are independent review conclusions, not additional Lean-certified results.

The accompanying manuscript distinguishes the physical CAR products of Section 20.1 from the Weyl-type formal vertices of Section 20.2. Its four-site example explicitly exhibits both nonzero discarded-channel contributions and a normalization mismatch. Those distinctions must remain part of the closure criterion.&#x20;

main.pdf



## 2. Exact finite objects and comparison domains

Let \\(\mathcal F_h\\) be the finite occupation Hilbert space on the centered momentum band

\\[ \Lambda_h^\*=\\{-h+1,\ldots,h\\},\qquad L=2h. \\]

For a charge vector \\(N=(N\_\nu)\_\nu\\), let

\\[ \mathcal H\_{N,K}=B(N,K),\qquad P\_{N,K}:\mathcal F_h\longrightarrow\mathcal H\_{N,K} \\]

be the actual joint charge and total-excitation-energy budget and its orthogonal projection.

For the polynomial oscillator system with modes \\(1\le m\le M\\), define the finite-dimensional subspace

\\[ \mathcal P\_{M,\le E} = \operatorname{span}\left\\{ X^\alpha: \sum\_{\nu,m}m\alpha\_{\nu m}\le E \right\\}. \\]

Its inherited inner product is

\\[ \langle X^\alpha,X^\beta\rangle = \delta\_{\alpha\beta} \prod\_{\nu,m}m^{\alpha\_{\nu m}}\alpha\_{\nu m}!. \\]

This is a total weighted-degree budget, not a Cartesian product of independently truncated oscillator occupations.

For example, with two species and \\(M=2\\),

\\[ X\_{R1}^{2}X\_{L1}\in\mathcal P\_{2,\le3}, \qquad X\_{R2}X\_{L2}\notin\mathcal P\_{2,\le3}. \\]

The polynomial space \\(\mathcal P\_{M,\le E}\\) is a finite inner-product carrier; the original multiplication and differentiation operators still act on the unrestricted polynomial algebra.

Let \\(p_N(\alpha)\\) denote the physical partition state constructed by applying the specified positive raw currents to the actual sector sea \\(\Omega_N\\). Define

\\[ U\_{N,E}^{(M)}X^\alpha=p_N(\alpha). \\]

When the exact finite Haldane Gram and completeness hypotheses hold through energy \\(E\\),

\\[ \langle U\_{N,E}^{(M)}X^\alpha, U\_{N,E}^{(M)}X^\beta\rangle = \langle X^\alpha,X^\beta\rangle, \\]

so \\(U\_{N,E}^{(M)}\\) is an isometric embedding into \\(B(N,E)\\).

There is an important distinction:

- If \\(M\ge E\\) and full Haldane completeness is available, \\(U\_{N,E}^{(M)}\\) is onto \\(B(N,E)\\).
- If \\(M\<E\\), its range generally contains only partitions with parts no greater than \\(M\\), and it is not onto the entire physical budget.

This affects every attempted operator-norm transport. An isometric embedding is not automatically a unitary between the full budget spaces.

### Finite bounded maps

Write \\(Q_E\\) for the weighted-degree projection on the polynomial space. Then

\\[ C\_{\nu m}^{E'\leftarrow E}=Q\_{E'}C\_{\nu m}|\_{\mathcal P\_{M,\le E}}, \qquad A\_{\nu m}^{E'\leftarrow E}=Q\_{E'}A\_{\nu m}|\_{\mathcal P\_{M,\le E}} \\]

are genuine bounded maps between finite-dimensional Hilbert spaces.

Using normalized monomials, one obtains

\\[ \left\\|C\_{\nu m}^{E'\leftarrow E}\right\\| \le \sqrt{m\left(\left\lfloor E/m\right\rfloor+1\right)}, \\]

and

\\[ \left\\|A\_{\nu m}^{E'\leftarrow E}\right\\| \le \sqrt{m\left\lfloor E/m\right\rfloor}. \\]

These are finite-regulator bounds, not bounds on unrestricted polynomial multiplication.

The actual physical fields also have bounded norm:

\\[ \\|c\_\nu(x)\\|=1 \\]

for the normalized unitary Fourier transform and unit-modulus species twist. Consequently,

\\[ \\|O\_{\mathrm{CDW}}(x)\\|\le1, \qquad \\|O\_{\mathrm{SC}}(x)\\|\le1. \\]

These finite CAR operators must not be replaced by formal vertices when defining the physical side of a comparison.

## 3. Exact finite-degree comparison theorem

This is the strongest positive result I recommend investigating first. It uses actual fermionic density operators and does not require a finite squeezed vacuum.

### 3.1 Operator dictionary

For \\(1\le m\le M\\), define the free-word substitution

\\[ \Theta_h(C\_{\nu m})=\rho\_{\nu,+m}, \qquad \Theta_h(A\_{\nu m})=\rho\_{\nu,-m}, \\]

and extend it to words by preserving multiplication order:

\\[ \Theta_h(g_1\cdots g_r) = \Theta_h(g_1)\cdots\Theta_h(g_r). \\]

Here \\(\rho\_{\nu,\pm m}\\) are the actual finite-band raw CAR currents, not formally postulated CCR operators.

This substitution exists on the free word algebra regardless of cutoffs. It is not, globally, a representation of the CCR quotient: the finite-CAR currents have edge corrections.

Let \\(\beta^{-1}\_{c,s}\\) denote the Bogoliubov generator substitution with \\(s\mapsto-s\\), extended multiplicatively to free words. It preserves word length and the adjoint.

For a generator word \\(w\\) of length at most \\(d\\), define the physical scalar

\\[ \Phi^{(d)}\_{h,N;c,s}(w) = \left\langle \Omega_N,\\, \Theta_h\bigl(\beta^{-1}\_{c,s}(w)\bigr) \Omega_N \right\rangle. \\]

This is a genuine finite-CAR matrix element. Notice that the physical observable is explicitly defined: it is a polynomial in actual finite density currents, with the Bogoliubov coefficients applied before evaluation.

It is not an interacting-ground-state expectation.

### 3.2 Candidate theorem: finite dressed-current moments

Proposition (conditional finite-degree comparison).

Assume:

1. The source charge vector \\(N\\) is admissible.
2. All generator labels satisfy \\(1\le m\le M\\).
3. The finite CAR current-action and partition-basis identities apply along every intermediate word path of excitation energy at most \\(dM\\).
4. The finite momentum-band margins needed by those identities hold. A conservative uniform condition suggested by the supplied `r2` convention is

\\[ \boxed{ 2dM+|N\_\nu|\le h \quad\text{for every species }\nu. } \\]

&#x20;  This condition is stronger than necessary for many individual words; the exact suffix margins remain the authoritative hypotheses.

Then, for every oscillator word \\(w\\) with \\(|w|\le d\\),

\\[ \boxed{ \Phi^{(d)}\_{h,N;c,s}(w)=\omega_P(w). } \tag{3.1} \\]

This equality is a finite collection of scalar moment equalities, not an equality of globally represented algebras.

For \\(c=1,s=0\\), it reduces to

\\[ \boxed{ \langle\Omega_N,\Theta_h(w)\Omega_N\rangle = \omega_0(w). } \tag{3.2} \\]

The proof below establishes the mathematical reduction; checking that the indicated uniform inequality entails every required Core suffix-margin theorem is a separate repository-verification obligation.

### 3.3 Derivation

First consider \\(s=0,c=1\\).

For a monomial basis state \\(X^\alpha\\), the polynomial annihilator satisfies

\\[ A\_{\nu m}X^\alpha = m\alpha\_{\nu m}X^{\alpha-e\_{\nu m}}, \\]

with zero output when \\(\alpha\_{\nu m}=0\\). Similarly,

\\[ C\_{\nu m}X^\alpha = X^{\alpha+e\_{\nu m}}. \\]

On the corresponding physical partition states, the current-action identity gives

\\[ \rho\_{\nu,+m}p_N(\alpha) = p_N(\alpha+e\_{\nu m}), \\]

provided the output remains within the allowed finite band, and

\\[ \rho\_{\nu,-m}p_N(\alpha) = m\alpha\_{\nu m}p_N(\alpha-e\_{\nu m}) \\]

under the appropriate input and suffix margins.

The second identity follows algebraically by commuting the negative current through the positive-current word and using its vacuum-annihilation property. In particular, each equal-mode contraction contributes \\(m\\), producing the multiplicity \\(m\alpha\_{\nu m}\\).

Thus, along an admissible path,

\\[ \Theta_h(g)\\,U\_{N,E}^{(M)}X^\alpha = U\_{N,E'}^{(M)}\pi_0(g)X^\alpha \\]

for either generator \\(g=A\_{\nu m}\\) or \\(C\_{\nu m}\\), with the appropriate input and output weights.

Now consider a word \\(w=g_1\cdots g_r\\), \\(r\le d\\). Its action proceeds from \\(g_r\\) to \\(g_1\\).

Starting at the polynomial vacuum, every successful creation increases the total weighted degree by at most \\(M\\); annihilation decreases it. Therefore every nonzero intermediate vector has energy bounded by

\\[ E_j\le rM\le dM. \\]

Induction over the factors gives

\\[ \boxed{ \Theta_h(w)\Omega_N = U\_{N,dM}^{(M)}\pi_0(w)1. } \tag{3.3} \\]

The vacuum corresponds to the constant monomial, and the partition map preserves its inner product. Consequently,

\\[ \langle\Omega_N,\Theta_h(w)\Omega_N\rangle = \langle1,\pi_0(w)1\rangle = \omega_0(w). \\]

For general \\(c,s\\), expand \\(\beta^{-1}\_{c,s}(w)\\). Each generator becomes a linear combination of two generators, so every resulting term still has word length at most \\(d\\) and mode labels at most \\(M\\).

Applying the free-vacuum identity term by term yields

\\[ \begin{aligned} \Phi^{(d)}\_{h,N;c,s}(w) &= \langle\Omega_N,\Theta_h(\beta^{-1}(w))\Omega_N\rangle\\\ &= \omega_0(\beta^{-1}(w))\\\ &= \omega_P(w). \end{aligned} \\]

This proves (3.1), assuming the current-action identities hold on the stated paths.

The important feature is that no compressed dressed annihilator is required to annihilate a finite-dimensional ground vector. The Bogoliubov transformation is applied to the observable dictionary, while the actual physical state on the CAR side remains the finite sea.

### 3.4 Sharper degree condition

The uniform \\(dM\\) bound may be unnecessarily restrictive.

For a particular monomial appearing after Bogoliubov substitution, read its factors from right to left. Let \\(e_j\\) denote its successive excitation energies whenever the action is nonzero.

Define

\\[ E\_\*(w)= \max\_{\substack{\text{nonzero terms in }\beta^{-1}(w)\\\ \text{nonzero intermediate paths}}} \max_j e_j. \\]

One may then impose the actual margin inequalities at those particular intermediate vectors rather than assume \\(E\_\*(w)=dM\\).

In practice, a simple conservative combinatorial bound is the largest cumulative weight of all creation generators encountered along a suffix of an expanded word. It can be evaluated before any CAR matrix calculation.

This yields a more useful theorem for a selected set \\(\mathcal W\\) of observables:

\\[ \forall w\in\mathcal W,\quad \Phi\_{h,N;c,s}(w)=\omega_P(w), \\]

provided every word in \\(\mathcal W\\) has verified finite-band margins.

The proof remains exact at fixed \\(h\\).

### 3.5 Concrete dressed moment

For one positive mode \\(m\\), the inverse transformation gives

\\[ \beta^{-1}(C\_{Rm})=cC\_{Rm}-sA\_{Lm}, \\]

\\[ \beta^{-1}(A\_{Rm})=cA\_{Rm}-sC\_{Lm}. \\]

Using the undressed oscillator vacuum,

\\[ \omega_0(A\_{\nu m}C\_{\nu m})=m, \qquad \omega_0(C\_{\nu m}A\_{\nu m})=0, \\]

one finds

\\[ \boxed{ \begin{aligned} \omega_P(A\_{Rm}C\_{Rm})&=mc^2,\\\ \omega_P(C\_{Rm}A\_{Rm})&=ms^2,\\\ \omega_P(A\_{Rm}A\_{Lm})&=-mcs. \end{aligned} } \tag{3.4} \\]

For example, choose \\(h=4\\), \\(L=8\\), \\(M=1\\), \\(d=2\\), and \\(N_R=N_L=0\\). The uniform bound is satisfied:

\\[ 2dM=4\le h. \\]

Under the verified current-action margins, the finite-CAR sea expectations of the corresponding inverse-Bogoliubov-substituted density words reproduce all three expressions in (3.4).

This gives a nonzero, interaction-parameter-dependent algebraic moment comparison at finite \\(L\\), without constructing a finite interacting vacuum.

### 3.6 Counterexample outside the correct dictionary

Suppose \\(s\ne0\\), and someone identifies the undressed physical current moment directly with the dressed oscillator moment.

The physical sea satisfies, under the vacuum current margin,

\\[ \rho\_{R,-m}\Omega_N=0, \\]

so

\\[ \langle\Omega_N, \rho\_{R,+m}\rho\_{R,-m}\Omega_N\rangle=0. \\]

But

\\[ \omega_P(C\_{Rm}A\_{Rm})=ms^2>0. \\]

Therefore

\\[ \boxed{ \langle\Omega_N, \rho\_{R,+m}\rho\_{R,-m}\Omega_N\rangle \ne\omega_P(C\_{Rm}A\_{Rm}) \quad(s\ne0). } \\]

The contradiction does not indicate failure of the exact finite moment theorem. It shows why an operator dictionary and a state comparison are two distinct ingredients.

In particular, (3.1) does not establish that the interacting CAR ground state has the dressed oscillator covariance.

## 4. Quantitative comparison with the actual physical fields

The current-moment theorem is exact but does not resolve the physical fermion-field problem. That requires an estimate retaining the original operators.

### 4.1 Three actual physical carriers

Let

\\[ \mathcal H_s=B(N_s,K_s),\quad \mathcal H_m=B(N_m,K_m),\quad \mathcal H_t=B(N_t,K_t). \\]

Let \\(A,B\\) be operators on the ambient finite CAR Hilbert space, with \\(B\\) acting first. For example, for CDW,

\\[ A=c_R(x)^\dagger,\qquad B=c_L(x). \\]

The physical operator is

\\[ O\_{\mathrm{phys}}=P_tABP_s, \\]

and the product through a prescribed intermediate budget is

\\[ O\_{\mathrm{seq}}=P_tAP_mBP_s. \\]

Their exact difference is

\\[ \boxed{ R=P_tA(I-P_m)BP_s. } \tag{4.1} \\]

No CCR hypothesis is needed for this identity.

### 4.2 Exact cancellation criterion

For any subspace \\(S\subseteq\mathcal H_s\\),

\\[ \boxed{ R|\_S=0 \iff P_tA(I-P_m)Bv=0 \quad\forall v\in S. } \tag{4.2} \\]

Two sufficient conditions are

\\[ BS\subseteq\operatorname{Ran}P_m \\]

or

\\[ A(I-P_m)BS\subseteq\ker P_t. \\]

The first says no intermediate energy escapes the budget. The second allows escape, but proves that all escaped paths are eliminated by the subsequent physical operation and target projection.

The distinction is important for local fermionic fields.

A density current \\(\rho\_{\nu,\pm m}\\) changes the total excitation energy by a controlled amount \\(m\\), as long as its finite-band action is valid. The spatial field

\\[ c\_\nu(x)=\frac1{\sqrt L}\sum\_{k\in\Lambda_h^\*} \chi\_{\nu,k}(x)a\_{\nu k} \\]

instead contains annihilation at every momentum. Even on a sector ground state, annihilating a particle far below the Fermi edge may produce a high-energy hole.

Thus the condition \\(K_m\ge K_s+M\\), useful for a current with mode labels bounded by \\(M\\), is not a general sufficient condition for a spatial fermion field. Its actual finite momentum support and excitation energies must be used.

### 4.3 An operator-norm estimate on a common carrier

For this theorem, assume all three budget spaces admit the full Haldane isometries

\\[ U_s:\mathcal P_s\overset{\sim}{\longrightarrow}\mathcal H_s,\quad U_m:\mathcal P_m\overset{\sim}{\longrightarrow}\mathcal H_m,\quad U_t:\mathcal P_t\overset{\sim}{\longrightarrow}\mathcal H_t. \\]

They are unitary between the indicated finite spaces, with their inherited inner products.

A sufficient mode-completeness choice is \\(M\ge\max(K_s,K_m,K_t)\\), accompanied by the required charge-sector margins.

Transport the physical operators:

\\[ \widehat A=U_t^\dagger P_tAP_mU_m, \qquad \widehat B=U_m^\dagger P_mBP_sU_s. \\]

Let \\(V_A:\mathcal P_m\to\mathcal P_t\\) and \\(V_B:\mathcal P_s\to\mathcal P_m\\) be independently specified bounded polynomial candidates. They may be derived from Chapter 14's ordered \\(w^+,w^-\\) prescription, but their equality with the physical maps is not assumed.

Define the measurable field errors

\\[ \epsilon_A=\\|\widehat A-V_A\\|,\qquad \epsilon_B=\\|\widehat B-V_B\\|. \\]

Because \\(U_m\\) is onto the complete intermediate budget,

\\[ U_t^\dagger P_tABP_sU_s = \widehat A\widehat B+\widehat R, \\]

where

\\[ \widehat R=U_t^\dagger R U_s. \\]

Subtract \\(V_AV_B\\), and write

\\[ \widehat A\widehat B-V_AV_B = (\widehat A-V_A)\widehat B+ V_A(\widehat B-V_B). \\]

The triangle inequality and submultiplicativity yield

\\[ \boxed{ \left\\| U_t^\dagger P_tABP_sU_s-V_AV_B \right\\| \le \\|R\\|+\epsilon_A\\|\widehat B\\| +\\|V_A\\|\epsilon_B. } \tag{4.3} \\]

For normalized lattice annihilation and creation fields, \\(\\|\widehat B\\|\le1\\), giving

\\[ \boxed{ \epsilon\_{\mathrm{product}} \le \\|R\\|+\epsilon_A+\\|V_A\\|\epsilon_B. } \tag{4.4} \\]

This is an exact finite-dimensional inequality.

All quantities are defined on specified Hilbert spaces. None requires a norm for uncompressed polynomial multiplication.

Equation (4.4) is a useful conditional comparison theorem, not a proof that its right-hand side is small. In particular, \\(\epsilon_A\\) and \\(\epsilon_B\\) are genuine physical obligations, not parameters to be declared zero.

The estimate becomes a falsifiable version-1 target by requiring explicit upper bounds, counterexamples, or exact calculations of these quantities on selected budgets.

### 4.4 If \\(M\\) does not give a complete intermediate basis

Suppose \\(U_m\\) is merely isometric, and let

\\[ Q_m^{(M)}=U_mU_m^\dagger\le P_m. \\]

Then

\\[ \begin{aligned} P_tABP_s ={}&P_tAQ_m^{(M)}BP_s\\\ &+P_tA(P_m-Q_m^{(M)})BP_s\\\ &+P_tA(I-P_m)BP_s. \end{aligned} \tag{4.5} \\]

This exposes two distinct discarded channels.

The last term is the intermediate budget residual \\(R\\).

The middle term,

\\[ R\_{\mathrm{mode}} = P_tA(P_m-Q_m^{(M)})BP_s, \\]

is leakage into physical budget states not represented by the selected \\(M\\)-mode polynomial subspace.

For an operator comparison using only that subspace, the estimate must include

\\[ \\|R\_{\mathrm{mode}}\\|. \\]

If the source or target polynomial image is also incomplete, additional source or target leakage must be tracked when claiming a norm estimate on the full physical budgets.

This decomposition prevents an especially subtle error: confusing omitted partition sectors with intermediate excursions above the energy budget.

## 5. Comparing states as well as operators

Suppose the physical source sector has a normalized density matrix \\(\rho\_{\mathrm{phys}}\\), supported on \\(\mathcal H_s\\). Transport it to the common polynomial carrier:

\\[ \widehat\rho\_{\mathrm{phys}} = U_s^\dagger\rho\_{\mathrm{phys}}U_s. \\]

Let \\(\sigma\\) be another normalized positive density matrix on that same finite carrier. The existence of \\(\sigma\\) is a separate assumption; it is not automatically supplied by \\(\omega_P\\).

For physical order-parameter maps \\(T_x,T_y:\mathcal P_s\to\mathcal P_t\\), let \\(V_x,V_y\\) be proposed finite candidates, and define

\\[ \epsilon_x=\\|T_x-V_x\\|, \qquad \epsilon_y=\\|T_y-V_y\\|, \qquad \delta=\\|\widehat\rho\_{\mathrm{phys}}-\sigma\\|\_1. \\]

Then

\\[ \begin{aligned} &\left| \operatorname{Tr}(\widehat\rho\_{\mathrm{phys}}T_x^\dagger T_y) - \operatorname{Tr}(\sigma V_x^\dagger V_y) \right|\\\ &\quad\le \left\\|T_x^\dagger T_y-V_x^\dagger V_y\right\\| +\delta\\|V_x\\|\\|V_y\\|\\\ &\quad\le \boxed{ \epsilon_x\\|T_y\\|+ \\|V_x\\|\epsilon_y+ \delta\\|V_x\\|\\|V_y\\|. } \end{aligned} \tag{5.1} \\]

For physical CDW/SC maps, \\(\\|T_y\\|\le1\\).

This gives a rigorous separation between operator error and state-comparison error.

If the physical ground state is not supported on the chosen budget, its projection probability must be treated as an additional state-truncation error. Renormalizing its projection without recording that probability would change the state under comparison.

### 5.1 Why the abstract state is insufficient

The algebraic functional

\\[ \omega_P=\omega_0\circ\beta^{-1} \\]

is positive and normalized, but it lives on the uncompressed oscillator algebra. A density matrix on \\(B(N,K)\\) representing all of its CCR moments cannot be inferred.

Indeed, if finite operators \\(A,C\\) represented the exact CCR globally, then

\\[ 0=\operatorname{Tr}[A,C] =m\dim B(N,K), \\]

a contradiction whenever \\(m\ne0\\) and the space is nonzero.

A finite state may match selected moments without representing the full algebra. This is exactly why degree-bounded comparisons are the appropriate target.

One can also formulate a comparison directly in terms of moment defects. Given a finite positive state \\(\sigma\\) and a prescribed finite word evaluator \\(D_d(w)\\), define

\\[ \mu_w= \left|\operatorname{Tr}(\sigma D_d(w))-\omega_P(w)\right|, \qquad |w|\le d. \\]

If a physical observable has transported representative \\(T_w\\), then

\\[ \boxed{ \left| \operatorname{Tr}(\widehat\rho\_{\mathrm{phys}}T_w)-\omega_P(w) \right| \le \\|T_w-D_d(w)\\| + \delta\\|D_d(w)\\| + \mu_w. } \tag{5.2} \\]

All three errors are finite and independently testable.

Equation (3.1) gives one exact construction where the moment error vanishes: the reference sea together with the inverse-Bogoliubov current dictionary. It does not make \\(\mu_w=0\\) for an independently chosen interacting state or vertex dictionary.

## 6. The five distinct errors

The Chapter 20 bridge should not combine these into an undifferentiated remainder.

| Error                   | Mathematical origin                                                 | Appropriate control                                                  |
| ----------------------- | ------------------------------------------------------------------- | -------------------------------------------------------------------- |
| Intermediate projection | \\(P_tA(I-P_m)BP_s\\)                                               | Exact range/kernel condition or norm                                 |
| Mode truncation         | Omitted oscillator modes or omitted partition states                | Explicit omitted-mode sums and range projections                     |
| Normal-order/prefactor  | Different ordered definitions and scalar factors                    | Direct ordered-contraction calculation                               |
| State comparison        | Physical density matrix versus chosen model state                   | Trace norm or selected moment defects                                |
| Dispersion              | Actual lattice energies versus linearized or current-model energies | Finite Hamiltonian difference and, when needed, spectral assumptions |

For example, if a finite phase expression contains

\\[ W_M=\sum\_{m=1}^M\frac{\chi_m}{m}\rho_m, \qquad |\chi_m|=1, \\]

then for \\(M'>M\\),

\\[ \\|W\_{M'}-W_M\\| \le \sum\_{m=M+1}^{M'}\frac{\\|\rho_m\\|}{m}. \tag{6.1} \\]

Because a raw finite current is a sum of bounded fermionic hopping operators, a coarse regulator-dependent estimate is

\\[ \\|\rho_m\\|\le \\#\mathrm{validPairs}(L,m)\le L. \\]

Therefore

\\[ \\|W\_{M'}-W_M\\| \le L\sum\_{m=M+1}^{M'}\frac1m. \\]

This bound is explicit but need not be small at fixed \\(L\\). A useful improvement would exploit the actual source/target budgets and Pauli restrictions rather than the ambient norm.

For a diagonal one-body dispersion difference \\(\Delta\varepsilon(k)\\), in a fixed \\(n\\)-fermion sector,

\\[ \left\\|d\Gamma(\Delta\varepsilon)\right\\| \le n\max_k|\Delta\varepsilon(k)|. \\]

This controls a Hamiltonian error, not automatically a ground-state error. A quantitative eigenvector or spectral-projection comparison generally requires an isolated spectral cluster and a gap estimate.

No such assumptions follow merely from the Bogoliubov identity.

## 7. Non-vacuity tests and counterexamples

### 7.1 Four-site discarded channel

The manuscript's explicit example takes

\\[ h=2,\quad L=4,\quad x=1, \\]

with source charge \\(N_s=(0,0)\\), intermediate charge \\(N_m=(0,-1)\\), and target charge \\(N_t=(1,-1)\\).

For \\(K_s=K_m=0\\), \\(K_t=1\\),

\\[ R\_{\mathrm{CDW}}\Omega\_{(0,0)} = -\frac14 |R\\{-1,0,1\\};L\\{0\\}\rangle. \\]

Hence

\\[ \boxed{\\|R\_{\mathrm{CDW}}\\|\ge\frac14.} \tag{7.1} \\]

This is an operator-norm lower bound, since the input ket is normalized.

When the target cutoff is reduced to \\(K_t=0\\), the same residual vanishes on the selected ground input. The two statements are consistent: cancellation is target- and subspace-dependent.

Moreover, the actual ground-to-ground CDW matrix element is

\\[ \langle\Omega\_{(1,-1)}, O\_{\mathrm{CDW}}(1)\Omega\_{(0,0)}\rangle =\frac{i}{4}. \\]

Thus a proposed operator retaining only this scalar ground-to-ground charge shift cannot reproduce the full target image at \\(K_t=1\\): it misses at least the displayed excited component of norm \\(1/4\\).

That does not rule out Chapter 14's more elaborate polynomial candidate, which can contain excited components. It rules out the stronger inference from one scalar ground coefficient to full operator equality.

### 7.2 Same-species finite-cutoff exchange

For the right-moving oscillator phase,

\\[ [Q_R(x),Q_R(y)] = 2iS_M(x-y)I, \\]

where

\\[ S_M(r)=\sum\_{m=1}^{M}\frac{\sin(2\pi mr/L)}m. \\]

The exact continuum sawtooth identity would give

\\[ S\_\infty(r)=\frac{\pi}{2}-\frac{\pi r}{L}, \quad 0\<r\<L, \\]

with the usual endpoint qualifications.

At \\(L=4\\), \\(M=1\\), \\(r=1\\),

\\[ S_1(1)=1,\qquad S\_\infty(1)=\frac{\pi}{4}. \\]

They are unequal. Thus the finite oscillator exchange commutator does not supply the cancellation needed for exact same-species fermionic exchange under the conventional continuum vertex prescription.

This already appears in the algebraic coefficients; it does not require assigning \\(t=1\\) to a formal exponential.

The auxiliary Klein factors do establish the appropriate mixed-species anticommutation, but they do not repair an arbitrary finite same-species oscillator phase.

### 7.3 The coincident-point normalization obstruction

For the four-site half-filled Slater sea,

\\[ \langle n_R(x)\rangle = \langle n_L(x)\rangle =\frac12. \\]

Because the two species are independent in that reference state,

\\[ \begin{aligned} \langle O\_{\mathrm{CDW}}^\dagger(x)O\_{\mathrm{CDW}}(x)\rangle &=\langle n_L(x)(1-n_R(x))\rangle=\frac14,\\\ \langle O\_{\mathrm{SC}}^\dagger(x)O\_{\mathrm{SC}}(x)\rangle &=\langle n_R(x)n_L(x)\rangle=\frac14. \end{aligned} \\]

The Section 20.2 Weyl-type formal construction instead gives the coincident formal correlator \\(L^{-2}=1/16\\).

Both calculations are internally meaningful, but they concern different operators and carriers.

Consequently the naive normalization identification fails, with scalar discrepancy

\\[ \boxed{ \frac14-\frac1{16}=\frac3{16}. } \\]

A corrected physical vertex proposal would need to justify its normalization and ordering independently; choosing a scalar specifically to eliminate this example would not prove the general field identity.

## 8. Charge, twist, and ordering obligations

Extending (3.1) to charge-changing words requires additional hypotheses.

For a word of successive Klein shifts, write

\\[ N^{(0)},N^{(1)},\ldots,N^{(q)} \\]

for its actual intermediate charge vectors, in right-to-left action order.

Every intermediate charge must be admissible in the finite CAR system. For a lowering step of species \\(\nu\\), the supplied condition

\\[ \operatorname{pairMargin}(h,K,N,\nu) \\]

requires `r2` for both \\(N\\) and \\(N-e\_\nu\\). The analogous raised-charge step must be treated using its actual input and target charges.

No unrestricted bilateral charge shift can be transported as a unitary on the entire finite charge interval. Only the required admissible arrows, with their individual source and target budgets, are available.

The physical Klein sign must remain

\\[ (-1)^{ \sum\_{\eta<\nu}(h+N\_\eta)+h+N\_\nu-1 }. \\]

A charge word must evaluate this sign after every preceding shift, not at a fixed unshifted label.

For nonperiodic species twists, the physical zero-mode factor \\(r\_\nu^x\zeta^{N\_\nu x}\\) also needs to match the proposed oscillator/charge dictionary. An untwisted auxiliary charge phase is not automatically the correct physical boundary phase.

Finally, Chapter 14's candidate has the order

\\[ \text{source phase} \longrightarrow \text{Klein lowering} \longrightarrow w^+\text{ Taylor action} \longrightarrow \text{budget transition} \longrightarrow w^-\text{ Taylor action}. \\]

The arrows indicate action order. This candidate is not the same definition as Section 20.2's Weyl-type formal vertex. Identifying them would require a separate ordered comparison, including contraction and normalization factors.

## 9. Dependency map and minimal mathematical theorem set

CH07, CH09–11: Finite energy grading, current commutators, partition Gram identities, completeness

Exact finite-word intertwining: Polynomial current words ↔ actual CAR density words under path margins

CH18–19 / A08: Bogoliubov substitution and positive oscillator functional

Theorem A: Exact dressed-current moments through degree \\(d\\)

CH13–14: Klein arrows, twists, finite polynomial field candidate

CH20: Actual CDW/SC operators and projection residual

Theorem B: Physical product error decomposition on common finite carriers

Theorem C: Conditional physical correlator estimate including a state defect

A minimal theorem list, in ordinary mathematical terms, is:

1. Finite path-intertwining theorem: Equation (3.3), with precise margins for positive and negative current actions.
2. Bogoliubov moment theorem: Equation (3.1), including a selected family of nontrivial degree-two and degree-four moments.
3. Charge-word extension: Exact transport of admissible finite Klein words, preserving source-dependent signs and twists.
4. Discarded-channel characterization: Equation (4.2), with concrete nonzero and exact-zero examples.
5. Finite operator-product comparison: Equations (4.3)–(4.5), including incomplete-mode-space leakage.
6. Conditional physical state comparison: Equation (5.1) or (5.2), with no assumed finite squeezed-vacuum vector.

The mathematical proofs of the general inequalities are supplied above. What remains is to establish the relevant physical dictionary defects and to verify the required finite-band margins against the exact existing source conventions.

## 10. Version-1 closure matrix

The following separates the levels of claim that the manuscript should report.

| Target                                         | Carrier and assumptions                                          | Baseline used / missing argument                                                                  | Obstruction and validation                                                                            |
| ---------------------------------------------- | ---------------------------------------------------------------- | ------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------- |
| Exact finite-current moments                   | Actual CAR sea and \\(\mathcal P\_{M,\le dM}\\); current margins | CH09–11, CH19/A08; verify uniform path-intertwining                                               | Edge effects outside margins; test \\(h=4,M=1,d=2\\)                                                  |
| Charge-changing selected moments               | Admissible charge sequence and total-energy budgets              | CH13 Klein kernel; establish full ordered charge-word transport                                   | Forbidden terminal charges, twists; test two successive shifts in opposite orders                     |
| Physical CDW/SC product identity with residual | \\(B(N_s,K_s)\to B(N_t,K_t)\\)                                   | Finite CH20 already supplies exact decomposition                                                  | \\(L=4\\), \\(K_m=0,K_t=1\\), nonzero \\(R\\)                                                         |
| Physical field–polynomial comparison           | Common finite partition Hilbert spaces; CH14 ordering            | CH14 provides a conditional criterion; ground-image equality and common physical residuals remain | A ground scalar is insufficient; compare full \\(Tv_0\\) and \\(Vv_0\\)                               |
| Interacting correlator bound                   | Common finite state and operator carriers                        | General estimate (5.1); determine operator errors and state defect                                | Finite squeezed-vacuum obstruction; use a directly specified finite Hamiltonian and density matrix    |
| Formal coefficientwise vertex correlator       | Uncompressed algebra and charge lattice; formal \\(t\\)          | CH19/A08 algebraic Wick theory; check manuscript ordering                                         | No \\(t=1\\) evaluation; test low coefficients and normalization                                      |
| Finite physical duality                        | Actual charge-sector CAR Hilbert spaces                          | Not supplied by algebraic parameter duality                                                       | Nonunitary finite charge shifts at boundaries; distinguish no-go from conditional subspace covariance |
| Continuum correlator interpretation            | Requires an analytic limiting family                             | Not part of version-1 finite bridge                                                               | Finite mode exchange differs from sawtooth; no continuum claim                                        |
| Finite CH21 spin/Umklapp                       | Actual spinful CAR sectors and finite shells                     | Finite CAR, Klein order, charge shifts, exact residuals                                           | No need for interacting oscillator-state or vertex equality                                           |

### What is unnecessary for finite CH21?

The proposed finite spinful/Umklapp developments do not logically require:

- a global CAR–CCR isomorphism;
- a finite squeezed vacuum satisfying every dressed-annihilator equation;
- physical fermion-field equality with a Mandelstam vertex;
- the formal CDW/SC Gaussian correlators to equal interacting CAR correlators;
- an exact finite-Fock CDW/SC duality;
- thermodynamic power laws or an analytic \\(t=1\\) vertex construction.

Finite CH21 does require the actual charge and spin definitions, signs, admissible sectors, projected products, and their leakage terms. A finite energy-shell Schrieffer–Wolff treatment additionally requires its own spectral-denominator assumptions.

These can be developed without waiting for a solution of the stronger Chapter 20 field reconstruction problem.

## 11. Recommended bounded research scope

For human review, I would separate the CH20b conclusions into three outcomes.

Accept an exact moment-comparison result if the finite-word theorem (3.1) is established with checked suffix margins, nontrivial dressed moments, and the precise current/Klein operator dictionary. This is a substantive bridge between physical finite currents and the algebraic oscillator model.

Accept a conditional physical-field comparison through (4.4) and (5.1), with the actual finite CAR field or bilinear on one side and the fixed Chapter 14 candidate on the other. Every unknown error must remain explicitly unknown until bounded or calculated. A result showing that an error remains nonzero is mathematically legitimate.

Keep general interacting vertex and state identification open unless the ground-image and common-residual hypotheses of CH14, together with a valid state comparison, are independently established.

The result should not be advertised as finite interacting bosonization merely because its current moments or formal vertex coefficients agree.

In particular, no-go statements close their precisely stated mathematical questions; they do not establish the originally desired equalities.

## 12. Remaining clarifying questions

Four specifications matter before choosing the definitive finite theorem.

1\. Which physical Hamiltonian determines the proposed interacting ground state? The Bogoliubov-transformed oscillator quadratic form and a selected finite CAR Hamiltonian need not have ground states related by the same transformation. Exact Hamiltonian, sector, and gap assumptions are needed for any state comparison.

2\. Which full source-to-target image is intended for the field comparison? The CH14 criterion requires \\(T\Omega_N=V\Omega_N\\) as a complete target vector. Ground-to-ground coefficients and one normalization do not determine it.

3\. Should the version-1 theorem apply to all words through degree \\(d\\), or to a selected physical word family? The latter may admit much sharper margins, especially for charge-ordered correlators.

4\. Is the intended polynomial operator the CH14 normal-ordered projected Taylor candidate or the CH20 Section 20.2 Weyl-type formal vertex? Their factor order and prefactors are different. A single physical comparison theorem cannot silently interchange them.

None of these prevents the exact current-moment result or the general finite error inequalities above.

## 13. Verified literature

The sources below were checked against journal/publisher records or original deposited manuscripts. Their continuum or infinite-sea results motivate the algebraic dictionary but do not establish the new finite-band comparison proposed here.

1\. Daniel C. Mattis and Elliott H. Lieb, “Exact Solution of a Many-Fermion System and Its Associated Boson Field,” Journal of Mathematical Physics 6, 304–312 (1965). DOI: [10.1063/1.1704281](https://doi.org/10.1063/1.1704281?utm_source=chatgpt.com). The original work identifies the central role of the anomalous current commutator in the filled-sea limit; it does not remove the trace obstruction for globally finite-dimensional CCR.&#x20;

[image](https://www.google.com/s2/favicons?domain=https://collaborate.princeton.edu\&sz=32)

Princeton University

+1



2\. F. D. M. Haldane, “‘Luttinger liquid theory’ of one-dimensional quantum fluids. I. Properties of the Luttinger model and their extension to the general 1D interacting spinless Fermi gas,” Journal of Physics C: Solid State Physics 14, 2585–2609 (1981). DOI: [10.1088/0022-3719/14/19/010](https://doi.org/10.1088/0022-3719/14/19/010?utm_source=chatgpt.com). Relevant to the low-energy charge/current description, but not a substitute for finite-band margin proofs.&#x20;

[image](https://www.google.com/s2/favicons?domain=https://collaborate.princeton.edu\&sz=32)

Princeton University

+1



3\. Jan von Delft and Herbert Schoeller, “Bosonization for beginners — refermionization for experts,” Annalen der Physik 510, 225–305 (1998). DOI: [10.1002/andp.19985100401](https://doi.org/10.1002/andp.19985100401?utm_source=chatgpt.com); arXiv: [cond-mat/9805275](https://arxiv.org/abs/cond-mat/9805275?utm_source=chatgpt.com). Relevant to finite-size bosonization, fermion-number-changing Klein factors and operator ordering. Its construction is not a proof of the specified finite-band, finite-charge identity.&#x20;

[image](https://www.google.com/s2/favicons?domain=https://onlinelibrary.wiley.com\&sz=32)

Wiley Online Library

+1



Final recommendation: The most defensible CH20b closure is an exact, degree-bounded comparison of physical CAR current moments with the abstract Bogoliubov functional, supplemented by a finite norm-and-state error theorem for the original CDW/SC operators. It gives a genuine positive result, preserves the known nonzero residuals, and makes stronger reconstruction claims independently falsifiable. It also permits finite CH21 to proceed without importing unproved interacting bosonization assumptions.



