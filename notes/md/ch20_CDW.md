# BOSONIZE-LEAN: Mathematical Reference Notes

## Part VI: Phase 6 Observables, Correlators & Duality

### Chapter 20: CDW Correlators and the Topological Duality Theorem

In Chapter 19, we established the exact algebraic kernels $D_r(Z)$ to measure direct density fluctuations. However, the most profound signatures of 1D quantum matter are not found in the raw density $\rho(x)$, but in macroscopic order parameters like the **Charge Density Wave (CDW)** and anomalous pairing fluctuations.

Because electrons in 1D cannot bypass each other, they tend to lock into ordered spatial patterns. To evaluate these phenomena algebraically on our finite lattice, we must construct these macroscopic order parameters directly from the fundamental discrete lattice fermions $c_{(\nu, x)}$. By evaluating the ground-state expectation values of these operators using the **Mattis-Mandelstam** bosonic exponentials (Chapter 14), we will recover exact finite-lattice correlation functions.

Furthermore, by analyzing these exact algebraic forms, we will formalize the **Topological T-Duality** of the 1D quantum fluid—a strict algebraic isomorphism within the energy budget.

#### 20.1 Macroscopic Order Parameters on the Lattice

The physics of 1D differs wildly from higher dimensions due to the geometry of the Fermi surface. In 2D or 3D, the Fermi surface is a continuous curve or volume. In 1D, the Fermi surface consists of exactly two discrete points in momentum space: $+k_F$ (Right-movers) and $-k_F$ (Left-movers).

**Physical Intuition (Backscattering and Nesting):**
Because there are only two Fermi points, an interaction that transfers a particle from the Left branch to the Right branch requires a momentum kick of exactly $q = 2k_F$. This is called **backscattering**. This geometric perfect matching (nesting) strongly drives the system to form a spatial ripple of charge with a period tied to $2k_F$.

**Definition 20.1 (CDW and Pairing Order Parameters).**
Using the chiral species index $\nu \in \{R, L\}$, we define the local macroscopic order parameters on the discrete lattice $\Lambda$ strictly using the fundamental fermionic operators:

The **Charge Density Wave (CDW)** operator transfers a particle across branches, generating the $2k_F$ density ripple:

$$
O_{CDW}(x) := c^\dagger_{(R, x)} c_{(L, x)} \tag{20.1}
$$

The **Anomalous Pairing (SC proxy)** operator destroys two particles from opposite branches:

$$
O_{SC}(x) := c_{(R, x)} c_{(L, x)} \tag{20.2}
$$

*(Note: True physical Cooper pairs in a BCS superconductor require binding fermions of opposite spins, e.g.,* $c_{\uparrow} c_{\downarrow}$*. Because our current model is strictly spinless,* $O_{SC}$ *acts as a mathematical proxy for pairing fluctuations. We will introduce true spinful symmetry in Chapter 21).*

**Lemma 20.2 (Bosonized Order Parameters on the Budget).**
By substituting the exact Mattis-Mandelstam dictionary (Theorem 14.7), we map these fermionic bilinears strictly into bosonic vertex operators acting on the budget subspace $\mathcal{B}_{K, \vec{N}_{max}}$. The Klein factors $F_R^\dagger F_L$ handle the exact species sector shifts, while the unnormalized Umbral phase fields $W^\pm(x)$ sum algebraically:

$$
O_{CDW}(x) \propto F_R^\dagger F_L \exp\left[ W^-_R(x) - W^-_L(x) \right] \exp\left[ W^+_R(x) - W^+_L(x) \right] \tag{20.3}
$$

$$
O_{SC}(x) \propto F_R F_L \exp\left[ W^-_R(x) + W^-_L(x) \right] \exp\left[ W^+_R(x) + W^+_L(x) \right] \tag{20.4}
$$

#### 20.2 Exact Evaluation of the Vertex Correlators

To calculate the correlation function $\omega_{\tilde{\Omega}} ( O_{CDW}^\dagger(x) O_{CDW}(y) )$, we must evaluate the expectation value of these exponentiated operators in the interacting Bogoliubov vacuum functional $\omega_{\tilde{\Omega}}$.

Because the algebra is exactly quadratic (nilpotent of step 2 on the budget), the Baker-Campbell-Hausdorff (BCH) formula holds exactly (Lemma 8.8). Pushing all lowering operators to the right and raising operators to the left pulls down exactly the commutator of the phase fields into a scalar exponent.

**Theorem 20.3 (Exact Finite-Lattice Correlator).**
By applying the exact algebraic BCH formula to the bosonized order parameters and evaluating over the interacting functional, the spatial correlation function yields exactly:

$$
\omega_{\tilde{\Omega}} \left( O_{CDW}^\dagger(x) O_{CDW}(y) \right) \propto \exp \left[ -2g \cdot D_1(x, y) \right] \tag{20.5}
$$


Where $g$ is the algebraic Luttinger parameter (defined via the hyperbolic parameters in Chapter 18), and $D_1(x, y)$ is the exact discrete logarithmic Green's function derived from the density modes in Chapter 19.

Following identical algebraic steps for the pairing operator, the correlator evaluates to:

$$
\omega_{\tilde{\Omega}} \left( O_{SC}^\dagger(x) O_{SC}(y) \right) \propto \exp \left[ -\frac{2}{g} \cdot D_1(x, y) \right] \tag{20.6}
$$

#### 20.3 Topological T-Duality

Looking closely at the exact algebraic results in Theorem 20.3, a profound structural symmetry emerges. The mathematical physics is completely invariant under the simultaneous exchange of the interaction strength $g \leftrightarrow 1/g$ and the macroscopic observables $O_{CDW} \leftrightarrow O_{SC}$.

In string theory and conformal field theory, this is the exact 1D analog of **Target-Space Duality (T-Duality)**, where physics on a circle of radius $R$ is identical to physics on a circle of radius $1/R$.

**Theorem 20.4 (The Exact Duality Isomorphism).**
Let $\mathfrak{A}_{\mathcal{B}}$ be the observable algebra on the budget subspace. We define the Duality map $\mathcal{D} : \mathfrak{A}_{\mathcal{B}} \to \mathfrak{A}_{\mathcal{B}}$ as the specific algebraic automorphism that swaps the symmetric and antisymmetric combinations of the Left and Right chiral branches.

Under this exact `AlgEquiv` mapping, the interacting Luttinger Hamiltonian $H_{\text{Lutt}}(g)$ evaluated with Luttinger parameter $g$ maps identically to the Hamiltonian evaluated with parameter $1/g$:

$$
\mathcal{D} \left( H_{\text{Lutt}}(g) \right) = H_{\text{Lutt}}(1/g) \tag{20.7}
$$


Furthermore, the local macroscopic order parameters strictly invert:

$$
\mathcal{D} (O_{CDW}) = O_{SC}, \quad \mathcal{D} (O_{SC}) = O_{CDW} \tag{20.8}
$$

#### 20.4 Technical Notes for the Lean 4 Formalization

1. **Defining the Order Parameters:**

   * $O_{CDW}$ and $O_{SC}$ must be defined purely as bilinear combinations of the fundamental $c_{(\nu, x)}$ operators inside `Module.End ℂ (FockSpace _)`.

   * Lemma 20.2 is then proven by applying the Mattis-Mandelstam equivalence (Theorem 14.7), triggering a strict rewrite into the budget space.

2. **The Exact BCH Evaluation (`truncated_exp`):**

   * Lean's proof of Theorem 20.3 must utilize the `truncated_exp` lemmas proven in Chapter 8. Because the operators commute to a scalar $[W^+, W^-] = D_1(x, y) \cdot I$, Lean's ring simplifier will successfully group the cross-terms in the expansion, isolating $e^{-D_1(x, y)}$.

3. **Defining the Duality Map** $\mathcal{D}$**:**

   * Define $\mathcal{D}$ strictly as an `AlgEquiv` over the complex numbers acting on the density mode generators. To prove Theorem 20.4, simply apply this `AlgEquiv` to the explicit definition of $H_{\text{Lutt}}$ from Chapter 17. Lean's `ring` tactic will automatically reshuffle the coefficients to output the inverted interaction strength $1/g$.

#### 20.5 Informal Physical Discussion (Beyond the Formal Lattice)

*Note: The following section provides standard physical intuition and limits that are not directly formalized as exact algebraic theorems in Lean 4.*

**The Mermin-Wagner-Ho Theorem and Fluctuations:**
In 3D systems, attractive interactions cause the vacuum to undergo spontaneous symmetry breaking, locking into a stable BCS superconducting ground state (True Long-Range Order). However, the **Mermin-Wagner-Ho Theorem** strictly forbids the spontaneous breaking of continuous symmetries in 1D at finite temperatures (and for ground states in many 1D quantum models) because low-dimensional quantum fluctuations are overwhelmingly strong.
This means neither a perfect CDW crystal nor a perfect BCS state can exist in 1D. Instead, the system exists in a critical state of *quasi-long-range order*, where the order parameters fluctuate violently but maintain algebraic (power-law) memory of each other across space.

**The Continuum Asymptotic Limit:**
For macroscopic distances $1 \ll \vert{}x-y\vert{} \ll L$, the exact discrete kernel $D_1(x,y)$ asymptotically approaches the continuous logarithm $\ln \vert{}x-y\vert{}$. If we substitute this continuous limit into our exact exponentials, we recover the celebrated non-integer power-law decays that define the Luttinger Liquid in the continuum:

$$
\langle O_{CDW}^\dagger(x) O_{CDW}(y) \rangle \sim \frac{1}{\vert{}x-y\vert{}^{2g}}
$$

$$
\langle O_{SC}^\dagger(x) O_{SC}(y) \rangle \sim \frac{1}{\vert{}x-y\vert{}^{2/g}}
$$


From this asymptotic view, the duality is physically intuitive: if we have repulsive interactions ($g < 1$), the CDW decay is slow ($2g < 2$, meaning dominant order), and SC is suppressed. If we introduce attractive interactions ($g > 1$), SC strictly dominates and CDW is suppressed.
