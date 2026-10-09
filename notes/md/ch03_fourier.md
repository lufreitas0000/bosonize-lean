### Chapter 3: Finite Fourier Transform

To ensure the exact algebraic nature of the bosonization mapping, we separate the finite character algebra from the Hilbert-space unitary normalization. This follows the formal strategy defined in [Appendix A01](../appendices/a01_fourier_scalars_and_characters.md).

**Definition 3.1 (Primitive Root of Unity).** Let $K$ be a field, and $\zeta \in K$ a primitive $L$-th root of unity. To avoid zero divisors obstructing orthogonality, we strictly require $(L : K) \neq 0$.

$$
\zeta^L = 1 \tag{3.1}
$$
$$
\forall m \in \{1, \dots, L-1\}, \quad \zeta^m \neq 1 \tag{3.2}
$$

Analytically, we will later instantiate this with $\zeta = e^{2\pi i / L}$ in $\mathbb{C}$.

**Definition 3.2 (Algebraic Character and Unscaled DFT).** For any momentum $k \in \Lambda^*$ and position $x \in \Lambda$, the algebraic character is defined as:

$$
\chi(k,x) = \zeta^{kx} \tag{3.3}
$$

We define the unscaled negative-sign analysis map $S$ and positive-sign synthesis map $T$:

$$
Sf(k) = \sum_{x \in \Lambda} f(x)\chi(-k,x) \tag{3.4}
$$
$$
Tg(x) = \sum_{k \in \Lambda^*} g(k)\chi(k,x) \tag{3.5}
$$

**Lemma 3.3 (Orthogonality & Unscaled Inversion).** By summing the geometric series over the valid field, the characters are orthogonal:

$$
\sum_{x \in \Lambda} \chi(k-k', x) = L \delta_{kk'} \tag{3.6}
$$

This leads directly to the unscaled inversion identities without requiring square roots:

$$
TS = L \cdot I, \qquad ST = L \cdot I \tag{3.7}
$$

**Definition 3.4 (Unitary Physical Normalization).** For the physical fermionic layers defined over $\mathbb{C}$, we isolate the normalization into a single real scalar $a = 1/\sqrt{L}$ satisfying $L a^2 = 1$. The unitary DFT operator $U$ and its exact inverse are defined as:

$$
U = a S, \qquad U^{-1} = U^\dagger = a T \tag{3.8}
$$

Applying this unitary normalization preserves the counting canonical anticommutation relations (CAR) without introducing mixed scalar scalings.

**Lemma 3.5 (Diagonalization of Difference Operators).** The umbral difference operators act strictly diagonally on the characters:

$$
\Delta \chi(k, \cdot) = (\zeta^k - 1)\chi(k, \cdot) \tag{3.9}
$$
$$
\nabla \chi(k, \cdot) = (1 - \zeta^{-k})\chi(k, \cdot) \tag{3.10}
$$

The exact algebraic discrete Laplacian eigenvalue is:

$$
\Delta\nabla \chi(k, \cdot) = (\zeta^k + \zeta^{-k} - 2)\chi(k, \cdot) \tag{3.11}
$$

Only upon evaluation in $\mathbb{C}$ with $\zeta = e^{2\pi i / L}$ does this algebraically reduce to the physical dispersion $-4\sin^2\left(\frac{\pi k}{L}\right)$.
