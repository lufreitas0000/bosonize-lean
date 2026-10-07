
### Chapter 3: Finite Fourier Transform

Before taking the transform, we must define the algebraic roots of unity used as the kernel.

**Definition 3.1 (Primitive Root of Unity).** Let $\zeta \in \mathbb{C}$ be a primitive $L$-th root of unity. This means $\zeta$ generates the cyclic group of order $L$:

$$
\zeta^L = 1 \tag{3.1}
$$

$$
\forall k \in \{1, \dots, L-1\}, \quad \zeta^k \neq 1 \tag{3.2}
$$

 Analytically, we choose $\zeta = e^{2\pi i / L}$.

**Definition 3.2 (DFT and Plane Waves).** For any momentum $k \in \Lambda^*$ and position $x \in \Lambda$, the plane wave pairing is:

$$
e_k(x) = \zeta^{kx} \tag{3.3}
$$

 The Discrete Fourier Transform operator $U : \ell^2(\Lambda) \to \ell^2(\Lambda^*)$ is defined by the matrix elements:

$$
U_{kx} = \frac{1}{\sqrt{L}}\zeta^{-kx} \tag{3.4}
$$

 The forward transform of a function $f$ is:

$$
\hat{f}(k) = \frac{1}{\sqrt{L}}\sum_{x \in \Lambda} f(x)\zeta^{-kx} \tag{3.5}
$$

**Lemma 3.3 (Diagonalization of Difference Operators).** The difference operators from Chapter 2 act strictly diagonally on the plane waves:

$$
\Delta e_k = (\zeta^k - 1)e_k \tag{3.6}
$$

$$
\nabla e_k = (1 - \zeta^{-k})e_k \tag{3.7}
$$

$$
\Delta\nabla e_k = -4\sin^2\left(\frac{\pi k}{L}\right)e_k \tag{3.8}
$$

**Lemma 3.4 (Orthogonality & Unitarity).** The plane waves are strictly orthogonal over both domains:

$$
\sum_{x \in \Lambda} \zeta^{(k-k')x} = L\delta_{kk'} \tag{3.9}
$$

$$
\sum_{k \in \Lambda^*} \zeta^{k(x-y)} = L\delta_{xy} \tag{3.10}
$$

 The operator $U$ is exactly unitary:

$$
U U^\dagger = I \tag{3.11}
$$

$$
U^\dagger U = I \tag{3.12}
$$

 The inverse transform is explicitly:

$$
f(x) = \frac{1}{\sqrt{L}}\sum_{k \in \Lambda^*} \hat{f}(k)\zeta^{kx} \tag{3.13}
$$
