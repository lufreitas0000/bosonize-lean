### Chapter 16: The Field-Theoretic Hamiltonian and Lattice Error

In Chapter 12, we proved that the fermionic kinetic energy operator ($\hat{P}$) is algebraically identical to the bosonic Sugawara Hamiltonian ($H_{\text{sug}}^{(M)} = \sum \rho_m \rho_{-m}$) on the energy budget subspace.

We construct a discrete Field Hamiltonian using exact Umbral differences ($\Delta$). The exact algebraic normalization adheres strictly to the corrections in [Appendix A06](../appendices/a06_chiral_fields_and_lattice_kernels.md).

#### 16.1 Definitions

**Definition 16.1 (The Discrete Field Hamiltonian).**
We define the real-space field Hamiltonian $H_{\text{field}}$ as the spatial sum over the lattice $\Lambda$ of the normal-ordered squared Umbral gradients of the dual fields:

$$
H_{\text{field}} := \sum_{x \in \Lambda} :\! \left( (\Delta \phi)(x) \right)^2 + \left( (\Delta \theta)(x) \right)^2 \!: \tag{16.1}
$$

Normal ordering applies *externally* to the squared field difference to prevent vacuum divergences.

*Lean 4 Proof Strategy:*
Define the normal-ordered gradient square in a separate symbol/word carrier with fixed linear evaluation. Prove the specific quadratic evaluation formula with all contraction terms before collapsing the spatial sum. Do not define normal ordering by changing equal represented operators inconsistently.

#### 16.2 Chiral Separation and Spatial Collapse

**Lemma 16.2 (Chiral Decomposition).**
Because the dual fields are symmetric and antisymmetric combinations of the orientations ($\phi = \varphi_{+1} + \varphi_{-1}$ and $\theta = \varphi_{+1} - \varphi_{-1}$), the cross-terms cancel:

$$
(\Delta \phi(x))^2 + (\Delta \theta(x))^2 = 2 \left[ (\Delta \varphi_{+1}(x))^2 + (\Delta \varphi_{-1}(x))^2 \right] \tag{16.2}
$$

*Lean 4 Proof Strategy:*
Expand $(X+Y)^2+(X-Y)^2$ with distributivity or `noncomm_ring`. The cross terms cancel without assuming X and Y commute. Apply current reorderings explicitly and use `ring` only for scalar coefficients; a commutative ring instance on all endomorphisms is unavailable.

**Lemma 16.3 (Spatial Collapse via DFT).**
Let $M \ge 1$ satisfy the no-aliasing condition $2M < L$. Substituting the Umbral gradient expansion of the chiral field (Lemma 15.5) and applying the spatial orthogonality constraint $\sum_{x} \zeta^{(m-n)x} = L \delta_{mn}$, both mixed terms in the square contribute, yielding an exact factor of $2L$:

$$
\sum_{x \in \Lambda} :\!(\Delta \varphi_\eta(x))^2\!: = 2L \sum_{m=1}^{M} \left( \frac{(\zeta^m - 1)(\zeta^{-m} - 1)}{m^2} \right) \rho_{m, \eta} \rho_{-m, \eta} \tag{16.3}
$$

*Lean 4 Proof Strategy:*
We will formalize the DFT of the chiral field from Lemma 15.5. The proof will proceed by substituting the expansion into the squared term, distributing the sum, and swapping the spatial sum with the momentum sums. We then apply the spatial orthogonality constraint (an auxiliary lemma: `sum_zeta_pow_eq_L_delta`). The $2L$ factor arises from the cross terms in the expansion when $n = -m$. The proof will rely on `Finset.sum` manipulation lemmas (`sum_mul`, `mul_sum`, `sum_comm`).

#### 16.3 The Lattice Dispersion Theorem

**Definition 16.4 (Lattice Dispersion Weight).**
For $1 \le m \le M$, let $\varepsilon(m)$ be the exact algebraic weighting factor:

$$
\varepsilon(m) := \frac{L}{m^2} (\zeta^m - 1)(\zeta^{-m} - 1) = \frac{4L}{m^2} \sin^2\left(\frac{\pi m}{L}\right) \tag{16.4}
$$

The algebraic form $(\zeta^m - 1)(\zeta^{-m} - 1)$ strictly avoids transcendental functions within the cyclotomic field.

*Lean 4 Proof Strategy:*
The dispersion weight $\varepsilon(m)$ will be defined as an element of the cyclotomic field `K`. We will define `ε` by $\varepsilon(m) := (L/m^2)(\zeta^m-1)(\zeta^{-m}-1)$. We must ensure $m \neq 0$ to avoid division by zero, which is guaranteed by the domain $1 \le m \le M$. The equality involving $\sin^2$ is purely descriptive in the algebraic cyclotomic setup and won't be part of the algebraic definition, but can be formalized as a separate equivalence lemma over `ℂ` if needed.

**Theorem 16.5 (The Exact Weighted Lattice Energy).**
Combining the factors of 2 from the decomposition and the DFT collapse, with mode cutoff $M$ satisfying $2M < L$ and budget margins ($2M + K + K_{\text{excursion}} + N_{\max} \le h$), $H_{\text{field}}^{(M)}$ evaluates on budget vectors to:

$$
\forall \psi \in \mathcal{B}_{K, \vec{N}_{max}}, \quad H_{\text{field}}^{(M)} \psi = 4 \sum_{\eta \in \{+1, -1\}} \sum_{m=1}^{M} \varepsilon(m) \rho_{m, \eta} \rho_{-m, \eta} \psi \tag{16.5}
$$

*Lean 4 Proof Strategy:*
This theorem chains Definition 16.1, Lemma 16.2, and Lemma 16.3. The proof strategy will start by applying Lemma 16.2 to `H_field` inside the sum, then distributing the sum over the two chiral sectors, and applying Lemma 16.3 to each. Finally, we rewrite using Definition 16.4 to collect the algebraic terms into $\varepsilon(m)$ and factor out the constant 4.

#### 16.4 The Total Sugawara Hamiltonian and Error Operator

**Definition 16.6 (Total Two-Branch Sugawara Hamiltonian).**
At mode cutoff $M$, we define the total two-branch Sugawara Hamiltonian acting on the multi-species budget by:

$$
H_{\text{sug}}^{(M)} := \sum_{\eta \in \{+1, -1\}} \sum_{m=1}^M \rho_{m, \eta} \rho_{-m, \eta} \tag{16.6}
$$

If $H_{\text{field}}^{(M)}$ were to equal exactly a scaled $H_{\text{sug}}^{(M)}$, the weight $\varepsilon(m)$ would have to be completely independent of $m$. We define an algebraic reference constant (e.g., $g_0 := \varepsilon(1)$ within the cyclotomic field, or $g_0 := 4\pi^2/L$ if working strictly over $\mathbb{C}$).

**Definition 16.7 (The Field Error Operator).**
The exact algebraic error operator at mode cutoff $M$ is:

$$
E_{\text{error}}^{(M)} := H_{\text{field}}^{(M)} - 4 g_0 H_{\text{sug}}^{(M)} = 4 \sum_{\eta \in \{+1,-1\}} \sum_{m=1}^{M} \left( \varepsilon(m) - g_0 \right) \rho_{m, \eta} \rho_{-m, \eta} \tag{16.7}
$$

*Lean 4 Proof Strategy:*
This will be defined as an operator on the Hilbert space. Assuming $g_0$ is defined as `ε(1)` and `H_sug` is already defined, `E_error` is straightforwardly defined as `H_field - 4 * g_0 * H_sug`. A small equality lemma will show that this definition equals the expanded sum form by substituting Theorem 16.5 and the definition of `H_sug`.

**Theorem 16.8 (Error Operator Kernel and Excited Witness).**
Let $g_0$ be an algebraic reference constant (e.g., $g_0 := \varepsilon(1)$).
(i) The error operator $E_{\text{error}}^{(M)}$ annihilates the joint sector ground state $|\vec{N}\rangle_0$ in every admissible charge sector, because every lowering mode $\rho_{-m,\eta}$ destroys $|\vec{N}\rangle_0$.
(ii) Any excited state in $\mathcal{B}_{K, \vec{N}_{\max}}$ composed purely of excitations in modes $m$ for which $\varepsilon(m) = g_0$ (such as pure mode $m=1$ excitations when $g_0 = \varepsilon(1)$) lies in $\ker(E_{\text{error}}^{(M)})$.
(iii) Nonzero action requires excitation in at least one mode $m \in \{1,\dots,M\}$ with $\varepsilon(m) \neq g_0$. When $M \ge 2$ and $\varepsilon(m) \neq g_0$ for some $m \ge 2$, the single-mode excitation $\psi = \rho_{m,\eta}|\vec{N}\rangle_0$ (provided margins hold) serves as an explicit nonzero witness:
$$
E_{\text{error}}^{(M)} \psi = 4 m (\varepsilon(m) - g_0) \psi \neq 0. \tag{16.8}
$$

*Lean 4 Proof Strategy:*
Part (i) proceeds by applying $E_{\text{error}}^{(M)}$ to $|\vec{N}\rangle_0$. In the sum form, each term contains $\rho_{-m,\eta} |\vec{N}\rangle_0 = 0$. For part (ii), on a state $\psi = \prod \rho_{1,\eta_j} |\vec{N}\rangle_0$, only $m=1$ terms can give non-zero mode commutators, but their coefficient is $\varepsilon(1) - g_0 = 0$, while all terms with $m \ge 2$ annihilate the state since no mode $m$ was created. For part (iii), the Heisenberg commutator $[\rho_{-m,\eta}, \rho_{m,\eta}] = m I$ produces the scalar factor $4 m (\varepsilon(m) - g_0) \neq 0$.

#### 16.5 Physical Motivation: Taylor Expansion and RG Scaling (Non-Formal)

> [!NOTE]
> The Taylor expansion and Wilsonian RG flow discussion below provide physical heuristics and motivation, distinct from the exact finite algebraic theorems above. An asymptotic scaling statement requires an explicitly defined sequence of lattice sizes and cutoffs $(L_n, M_n)$.

By Taylor expanding the sine-squared weight factor over $\mathbb{C}$:
$$
\varepsilon(m) - g_0 \propto - \frac{m^2}{L^3} \tag{16.9}
$$
Because the error coefficient scales proportionally to $m^2$, translating this back into spatial derivatives via Fourier transform suggests that the lattice error corresponds formally to a higher spatial derivative perturbation in the continuum:
$$
E_{\text{error}} \sim \int dx \left[ (\partial^2_x \phi)^2 + (\partial^2_x \theta)^2 \right] \tag{16.10}
$$
In the formal language of Wilsonian Renormalization Group (RG) flow, higher spatial derivatives possess higher scaling dimensions and are irrelevant operators in the infrared limit, explaining the emergence of the continuum Luttinger Liquid.


#### Constructive realization in Lean

The preceding theory and proof strategies are preserved as the reference exposition. The verified finite construction now realizes its quadratic-symbol Hamiltonian, exact weighted energy, and single-excitation witnesses. The earlier suggestion of a separate cyclotomic field is realized here by exact algebra in the complex numbers. The Taylor and RG discussion remains physical motivation.

**The finite model and what normal ordering acts on.** Put $L=2h$. Spatial points lie in the cyclic lattice $\mathbb Z/L\mathbb Z$, and states lie in the actual finite occupation Hilbert space of the multispecies fermion model. Each branch selects a distinct species and the oriented field already constructed in Chapters 15 and Appendix A06. All operators act on that full carrier. The energy restriction concerns the input vector's total excitation across species, with each species charge fixed; no intermediate budget projection is inserted between currents.

The retained labels have a branch, an index $i\in\{0,\ldots,M-1\}$, and a creator flag. Their physical momentum is $m=i+1$, so the represented modes are positive and denominators never involve zero. A creator represents $\rho_m$; an annihilator represents $\rho_{-m}$. A quadratic symbol assigns a complex coefficient to each **ordered pair** of labels. Raw evaluation uses the pair's original order. Normal evaluation swaps an annihilator followed by a creator into creator–annihilator order and leaves the other pairs in their original order. Evaluation is linear in these coefficients. It is a construction on symbols: the proof does not assign a normal-ordering operation to arbitrary operators that happen to have several symbol representations.

The gradient coefficients expand the exact periodic difference of the existing oriented chiral field. They retain $i/m$, the orientation and the full multipliers $\zeta^{\pm\eta m}-1$, for a primitive $L$-th root $\zeta$. This identifies the symbols being squared with the actual finite differences; it does not replace them by spectral or continuum derivatives.

**Why the weighted coefficient is four.** At the level of ordered quadratic coefficients, the right/left cross terms in the sum of the two dual-field squares cancel separately. Thus linear normal evaluation gives twice the sum of the two chiral squares. For a single chirality, expand its ordered pair sum and then sum over spatial points. Character orthogonality removes same-sign frequencies $\pm(m+n)$, since
$$
1\le m,n\le M,\qquad 0<m+n\le2M<L.
$$
For opposite signs it retains exactly $m=n$. The two ordered cross pairings each contribute the spatial factor $L$. After prescribed normal ordering both yield $\rho_m\rho_{-m}$, so together they give $2L$. Combining this with the dual-field factor of two yields
$$
H_{\mathrm{field}}\psi
=4\sum_{\eta\in\{R,L\}}\sum_{m=1}^{M}
\varepsilon(m)\rho_{m,\eta}\rho_{-m,\eta}\psi,
\qquad
\varepsilon(m)=\frac{L}{m^2}(\zeta^m-1)(\zeta^{-m}-1).
$$
This ordered-symbol collapse uses finite Fourier orthogonality rather than a global scalar current commutator. The approved budget theorem retains $h>0$, $M\ge1$, $2M<L$, root primitivity, and both sufficient branch margins
$$
2M+K+|N_\eta|\le h.
$$
For an input in the enlarged budget $K+e$, the excursion version retains $2M+K+e+|N_\eta|\le h$. This explicitly matches the bound to the input on which the identity is used.

**Ground and single-excitation error.** The implemented reference is exactly $g_0=\varepsilon(1)$. Subtracting its Sugawara contribution gives the weighted error in (16.7) under the same budget hypotheses. An admissible ground ket belongs to budget zero, is nonzero, and is killed by every positive-mode annihilator $\rho_{-n}$. Consequently the ordered weighted error kills that ground ket.

For $1\le m\le\min(M,K)$, consider the actual single excitation
$$
\psi_{m,\eta}=\rho_{m,\eta}|\vec N\rangle_0.
$$
The current budget map puts it in budget $K$. Its nonzeroness follows from applying the **restricted** identity $[\rho_{-m},\rho_m]|\vec N\rangle_0=m|\vec N\rangle_0$: a zero excited ket would force the nonzero ground ket to vanish. More generally, applying the lowering mode to the right ground suffix gives zero unless its species and momentum match those of the excitation. In the matching case it gives $m|\vec N\rangle_0$. Cross-species terms vanish by actual species commutation. The finite weighted sum therefore gives exactly
$$
E_{\mathrm{error}}\psi_{m,\eta}
=4m\bigl(\varepsilon(m)-\varepsilon(1)\bigr)\psi_{m,\eta}.
$$
At $m=1$ this proves zero error for one first-mode excitation. If the weight differs from the reference, it proves both a nonzero ket and nonzero error action. The stronger statement in part (ii) of Theorem 16.8 about arbitrary products of reference-mode creators is retained as reference theory; this batch does not prove that general word theorem or characterize the full kernel.

**A concrete nonzero error.** Choose $h=8$, $M=2$, $K=2$, zero charges, two distinct species and the primitive root $z=\zeta_{16}$. The margins hold because $2M+K=6\le8$, and $2M=4<16$. The weight gap is proved algebraically. Primitivity gives $z\ne0,1$; an assumed equality $\varepsilon(2)=\varepsilon(1)$, after clearing its nonzero denominators, implies $(z-1)^4=0$, contradicting $z\ne1$. The right-branch mode-two ket is therefore a genuine nonzero excited-error witness.

These results are exact finite complex algebra. They do not prove the sine characterization or positivity of the dispersion, an analytic limit, the Taylor remainder, RG irrelevance, or a complete error-kernel classification. The original descriptions of those broader ideas remain visible above with this distinction.

The [formal source](../../Bosonize/Core/Ch16FieldHamiltonian.lean) and [companion notebook](../../docs/companion/Bosonize/Core/Ch16FieldHamiltonian.md) record the exact hypotheses, declaration mapping and verification evidence. The proved staging batch passed fresh Phase B compiler and axiom checks; Phase C promotion and the independent review of this explanatory addition are pending at preparation time.


Independent final pedagogical reviewer `/root/characters` returned PASS for all
five documents after the link and historical-prose corrections. Both complete
reference prefixes are preserved, declaration mappings and predicted promoted
hashes are checked, the mathematics matches the proved contracts, and scope
limitations are explicit. No required findings remain. This review precedes the
runner's promoted compiler/axiom/CI acceptance and does not replace those gates.
