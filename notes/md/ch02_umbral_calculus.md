### Chapter 2: Umbral Calculus Core

We establish the formal algebraic foundations of the discrete calculus. In mathematical physics, difference operators are frequently defined ad hoc on specific domains like $\mathbb{Z}$ or the continuum. In the formal Lean approach (`Bosonize.Ch02`), we separate the minimal algebraic requirements on the coordinate domain $S$ and the scalar coefficients $R$ from any specific lattice realization.

#### 2.1 The Abstract Setting: Domain $S$ and Coefficient Ring $R$

**Algebraic Requirements:**

1. **The Coordinate Domain $(S, +, 1)$:** $S$ is any additive abelian group equipped with a distinguished "unit step" element $1 \in S$ (typeclasses `[AddCommGroup S] [One S]`). The shift operations require only that addition is commutative and invertible so that transitions $x \mapsto x + 1$ and $x \mapsto x - 1$ form mutual inverse bijections.

2. **The Scalar Ring $R$:** $R$ is an arbitrary commutative ring (`[CommRing R]`). No division, characteristic zero, or topological structure is assumed for the operator algebra or the Leibniz identities.

3. **The Function Module:** We study the $R$-module of functions $R^S \equiv (S \to R)$, which forms both an $R$-module and an associative, commutative $R$-algebra under pointwise addition, scalar multiplication, and pointwise multiplication. The operator space is the non-commutative algebra of $R$-linear endomorphisms:
$$
\mathrm{End}_R(R^S) := \mathrm{Hom}_R(R^S, R^S)
$$
where composition $(A \circ B)(f) = A(B(f))$ corresponds to operator multiplication $A B$ (acting right-to-left).

**Concrete Canonical Examples:**

- **Example A (The Infinite 1D Lattice):** $S = \mathbb{Z}$ with standard addition and $1 \in \mathbb{Z}$. Here functions are bilateral sequences $f : \mathbb{Z} \to R$.

- **Example B (The Periodic Spatial Lattice):** $S = \mathbb{Z}/L\mathbb{Z}$ (`Ch01.Lattice L`) with modular addition and residue $1 \bmod L$. Because $S$ is finite, functions form the finite-dimensional carrier $R^L$.

---

**Definition 2.1 (Umbral Operators).** We define the canonical linear endomorphisms in $\mathrm{End}_R(R^S)$:

1. **The Forward Shift Operator $E$:**
$$
(E f)(x) := f(x+1) \tag{2.1}
$$

2. **The Backward Shift (Inverse Shift) Operator $E^{-1}$:**
$$
(E^{-1} f)(x) := f(x-1) \tag{2.1a}
$$
*Group Inversion Identity (`shift_inverse`, `inverse_shift_shift`):*
Because $(x + 1) - 1 = x$ and $(x - 1) + 1 = x$ in any additive group, $E \circ E^{-1} = E^{-1} \circ E = I$.

3. **The Identity Operator $I$:**
$$
(I f)(x) := f(x) \tag{2.2}
$$

4. **The Forward Difference Operator $\Delta$:**
$$
\Delta := E - I, \qquad (\Delta f)(x) = f(x+1) - f(x) \tag{2.3}
$$

5. **The Backward Difference Operator $\nabla$:**
$$
\nabla := I - E^{-1}, \qquad (\nabla f)(x) = f(x) - f(x-1) \tag{2.5}
$$

6. **The Discrete Laplacian Operator $\Delta\nabla$:**
The discrete Laplacian is defined unambiguously by operator composition:
$$
\Delta\nabla := \Delta \circ \nabla \tag{2.7}
$$
Evaluating the composition in the operator algebra $\mathrm{End}_R(R^S)$:
$$
\Delta \circ \nabla = (E - I)(I - E^{-1}) = E - I - I + E^{-1} = E + E^{-1} - 2I
$$
Acting on any function $f \in R^S$:
$$
(\Delta\nabla f)(x) = f(x+1) + f(x-1) - 2f(x) \tag{2.7a}
$$

*Lean 4 Formal Construction:*
Defined in `Ch02UmbralCalculus.lean` as bundled `LinearMap` structures:

- `shift` and `inverseShift` map $f \mapsto (x \mapsto f(x \pm 1))$.

- `forwardDiff := shift - identity`, `backwardDiff := identity - inverseShift`.

- `laplacian := forwardDiff.comp backwardDiff`.

---

**Lemma 2.2 (Exact Discrete Leibniz Rules).** For any functions $f, g \in R^S$ over an arbitrary commutative ring $R$, the discrete derivative satisfies two asymmetric Leibniz product rules without any truncation:

$$
\Delta(fg) = (\Delta f)g + (Ef)(\Delta g) \tag{2.8}
$$

$$
\Delta(fg) = f(\Delta g) + (\Delta f)(Eg) \tag{2.9}
$$

*Proof and Algebraic Mechanism:*
Evaluating the LHS at an arbitrary point $x \in S$:
$$
\Delta(fg)(x) = f(x+1)g(x+1) - f(x)g(x)
$$
In any ring $R$, we apply the non-infinitesimal algebraic identity:
$$
a b - c d = (a - c) d + a (b - d) = c (b - d) + (a - c) b
$$
Setting $a = f(x+1)$, $b = g(x+1)$, $c = f(x)$, $d = g(x)$:

- The first grouping gives $(f(x+1) - f(x))g(x) + f(x+1)(g(x+1) - g(x)) = (\Delta f)(x)g(x) + (Ef)(x)(\Delta g)(x)$, yielding (2.8).

- The second grouping swaps the role of $f$ and $g$, yielding (2.9).
No limits, infinitesimals, or division by $h \to 0$ are needed; this is an identity of pure ring algebra.

---

**Lemma 2.3 (Summation by Parts on Periodic Lattices).** When the coordinate domain is the finite periodic lattice $\Lambda = \mathbb{Z}/L\mathbb{Z}$ with $L > 0$, the forward difference $\Delta$ and backward difference $\nabla$ are exact negative adjoints under the summation pairing $\langle f, g \rangle := \sum_{x \in \Lambda} f(x) g(x)$:

$$
\sum_{x \in \Lambda} f(x) \Delta g(x) = - \sum_{x \in \Lambda} (\nabla f)(x) g(x) \tag{2.10}
$$

*Lean 4 Proof Strategy & Reindexing Equivalence:*

1. Expand the sum: $\sum_x f(x)(g(x+1) - g(x)) = \sum_x f(x)g(x+1) - \sum_x f(x)g(x)$.

2. The translation map $e : \Lambda \to \Lambda$ given by $e(x) = x + 1$ is an equivalence (`Equiv`) of finite sets with inverse $e^{-1}(x) = x - 1$.

3. By Lean's `Equiv.sum_comp`:
   $$
   \sum_{x \in \Lambda} f(x) g(x+1) = \sum_{x \in \Lambda} f(x-1) g(x)
   $$

4. Recombining yields:
   $$
   \sum_{x \in \Lambda} f(x-1) g(x) - \sum_{x \in \Lambda} f(x) g(x) = - \sum_{x \in \Lambda} (f(x) - f(x-1)) g(x) = - \sum_{x \in \Lambda} (\nabla f)(x) g(x)
   $$
Because $\Lambda$ is a compact quotient group without boundaries, no boundary remainder arises.

---

**Lemma 2.4 (Algebraic Newton Expansion).** In $\mathrm{End}_R(R^S)$, the shift operator powers $E^n$ expand as a finite polynomial in the forward difference $\Delta$:

$$
E^n = \sum_{k=0}^n \binom{n}{k} \Delta^k \tag{2.11}
$$

*Proof via Algebra Commutation:*
In the ring $\mathrm{End}_R(R^S)$, $E = \Delta + I$. Because $I$ is the identity endomorphism, $\Delta$ and $I$ commute: $[\Delta, I] = 0$. By Mathlib's `Commute.add_pow`:
$$
(\Delta + I)^n = \sum_{k=0}^n \binom{n}{k} \Delta^k I^{n-k} = \sum_{k=0}^n \binom{n}{k} \Delta^k
$$
Evaluating on any test function $f \in R^S$ yields the classical Gregory-Newton interpolation formula without approximation:
$$
f(x+n) = \sum_{k=0}^n \binom{n}{k} (\Delta^k f)(x) \tag{2.11a}
$$

---

**Definition 2.5 (Formal Polynomial Umbral Map and Heisenberg Pair).**

1. **The Falling Factorial Polynomials:** For $n \in \mathbb{N}$, we define $X^{\underline{n}} \in R[X]$ as the monic polynomial of degree $n$:
$$
X^{\underline{0}} := 1, \qquad X^{\underline{n}} := \prod_{k=0}^{n-1} (X - k) = X(X-1)\cdots(X-n+1) \tag{2.12a}
$$
In Lean (`falling_factorial_succ`), $X^{\underline{n+1}} = X^{\underline{n}} (X - n)$.

2. **The Umbral Intertwining Map $\Phi$:** The linear map $\Phi : R[X] \to R[X]$ is defined on the standard monomial basis $\{X^n\}_{n \ge 0}$ by:
$$
\Phi(X^n) := X^{\underline{n}} \tag{2.12}
$$
and extended linearly to all polynomials via `Polynomial.lsum`.

3. **The Position Multiplier Operator $\beta$:** On the infinite integer domain $S = \mathbb{Z}$, we define the linear endomorphism $\beta \in \mathrm{End}_R(R^\mathbb{Z})$:
$$
(\beta f)(x) := x f(x-1) \tag{2.13}
$$
Notice the backward shift $x-1$; this shift is strictly necessary to balance the forward difference $\Delta$.

---

**Lemma 2.6 (Umbral Intertwining and the Exact Heisenberg Pair).**

1. **Intertwining the Continuum and Discrete Derivatives:**
Let $D = \frac{d}{dX} : R[X] \to R[X]$ be the formal algebraic derivative ($D(X^n) = n X^{n-1}$). Let $\Delta_{\mathrm{poly}} : R[X] \to R[X]$ be the polynomial difference operator defined by $(\Delta_{\mathrm{poly}} p)(X) := p(X+1) - p(X)$. Then $\Phi$ intertwines continuous derivation and discrete difference:
$$
\Phi \circ D = \Delta_{\mathrm{poly}} \circ \Phi \tag{2.14}
$$

*Proof (`umbral_commutation`):*
It suffices to check the basis vectors $X^n$.

- For $n = 0$: $D(1) = 0$ and $\Delta_{\mathrm{poly}}(1) = 0$.

- For $n \ge 1$: $\Phi(D(X^n)) = \Phi(n X^{n-1}) = n X^{\underline{n-1}}$.
On the other hand, applying the discrete difference to the falling factorial:
$$
\Delta_{\mathrm{poly}} X^{\underline{n}} = (X+1)^{\underline{n}} - X^{\underline{n}} = n X^{\underline{n-1}}
$$
Thus $\Delta_{\mathrm{poly}}(\Phi(X^n)) = \Delta_{\mathrm{poly}}(X^{\underline{n}}) = n X^{\underline{n-1}} = \Phi(D(X^n))$.

2. **The Exact Discrete Heisenberg Commutator:**
On the function module $R^\mathbb{Z}$, the operators $\Delta$ and $\beta$ satisfy the exact Canonical Commutation Relation (CCR):
$$
\Delta \beta - \beta \Delta = I \tag{2.15}
$$

*Proof (`heisenberg_pair_operator`):*
Evaluating on any test function $f : \mathbb{Z} \to R$ at coordinate $x \in \mathbb{Z}$:
$$
(\Delta(\beta f))(x) = (\beta f)(x+1) - (\beta f)(x) = (x+1)f(x) - x f(x-1)
$$
$$
(\beta(\Delta f))(x) = x (\Delta f)(x-1) = x (f(x) - f(x-1)) = x f(x) - x f(x-1)
$$
Subtracting the two expressions:
$$
(\Delta \beta - \beta \Delta)(f)(x) = \big[(x+1)f(x) - x f(x-1)\big] - \big[x f(x) - x f(x-1)\big] = (x+1 - x) f(x) = f(x) = (I f)(x)
$$
This establishes $[\Delta, \beta] = I$ identically.

3. **No-Go Theorem for Finite-Dimensional Matrix Realizations:**
*Theorem (`finite_dimensional_no_go`):* Let $K$ be any field of characteristic zero, and let $n > 0$ be a strictly positive integer. There exist **no** $n \times n$ matrices $A, B \in \mathrm{Mat}_{n \times n}(K)$ satisfying the commutation relation:
$$
[A, B] = A B - B A = I_n
$$

*Proof via the Trace Identity:*
Taking the matrix trace on both sides:
$$
\mathrm{Tr}([A, B]) = \mathrm{Tr}(AB - BA) = \mathrm{Tr}(AB) - \mathrm{Tr}(BA) = 0
$$
due to the cyclic invariance of the trace. However:
$$
\mathrm{Tr}(I_n) = \sum_{i=1}^n 1_K = n \cdot 1_K
$$
In any field of characteristic zero, $n \cdot 1_K \ne 0$ for $n > 0$. Hence $0 = n \ne 0$, a contradiction.
*Pedagogical Consequence:* This fundamental obstruction proves why exact quantum-mechanical position-momentum Heisenberg pairs and umbral operators cannot be realized as finite-dimensional matrix algebras. They require infinite-dimensional function modules (such as $R^\mathbb{Z}$) or must be truncated into projective/central extensions as in lattice CCR/CAR.
