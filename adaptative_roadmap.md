# Adaptive Roadmap: `bosonize-lean`

> **Role & Purpose:** Complements `README.md` by defining the Agile/Kanban pipeline, sprint goals, and R&D tracking for the 1D Constructive Bosonization project.

---

## 1. Project Status & Current Baseline

* **Notes Status (COMPLETED):** All foundational notes across Chapters 1 through 21 and Appendices A01 through A10 are formalized in `notes/md/` and `notes/appendices/`, complete with:
  * Discrete algebraic definitions (nilpotent exponentials, budget subspaces $\mathcal{B}_{K, \vec{N}_{\mathrm{max}}}$).
  * Exact equalities (no vague $\propto$ approximations, zero-mode Klein factor tracking).
  * Lean 4 proof strategies and auxiliary lemmas under every definition, lemma, and theorem.
* **Goal:** Incrementally translate these verified notes into compiled, zero-`sorry` Lean 4 code in `Bosonize/Core/`.

---

## 2. Adaptive Kanban Pipeline

```
+-----------------------------------------------------------------------------------------------+
|                                     BOSONIZE-LEAN KANBAN                                      |
+------------------------------------+--------------------------+-------------------------------+
| SPRINT 1: DISCRETE CORE ALGEBRA    | SPRINT 2: VERTEX ALGEBRAS| BACKLOG: ADVANCED EXTENSIONS  |
+------------------------------------+--------------------------+-------------------------------+
| [ ] CAR Algebra on finite lattice  | [ ] Sugawara Hamiltonians| [ ] Refermionization at K=1/2 |
| [ ] Finite Budget Subspace B_K     | [ ] Mattis-Mandelstam    |     (Luther-Emery Dirac mass) |
| [ ] Nilpotent Polynomial expNil    |     Vertex Dictionary    | [ ] Boundary Impurity & vDS   |
| [ ] Discrete Chiral Density Modes  | [ ] Interacting Pairing  |     Majorana zero-mode        |
| [ ] Kac-Moody Central Extension    |     Bogoliubov Transform | [ ] Non-Abelian SU(2)_1 WZW   |
|     commutation proof              | [ ] T-Duality AlgEquiv   |     Current Algebra           |
+------------------------------------+--------------------------+-------------------------------+
```

---

## 3. Sprint Specifications

### Sprint 1: The Theoretical Minimum (Core Kinematics)
* **Epic B-01: Discrete Lattice & CAR Module**
  * Formalize periodic lattice $\Lambda = \mathbb{Z}/L\mathbb{Z}$ and reciprocal lattice $\Lambda^*$.
  * Define the CAR algebra as a quotient of the free tensor algebra or matrix endomorphisms on the exterior algebra $\bigwedge \mathbb{C}^L$.
  * Auxiliary lemmas: CAR canonical anticommutators $\{c_p, c_q^\dagger\} = \delta_{pq}$.
* **Epic B-02: The Energy Budget Space**
  * Formalize $\mathcal{B}_{K, \vec{N}_{\mathrm{max}}}$ as a finite-dimensional submodule.
  * Prove margin stability: applying low-mode density operators $\rho_{\pm m}$ preserves the budget if the excitation energy is strictly bounded.
* **Epic B-03: Truncated Nilpotent Exponential (`expNil`)**
  * Define `expNil(X)` as a finite polynomial sum up to degree $N_{\mathrm{nil}}$.
  * Prove the exact finite Baker-Campbell-Hausdorff (BCH) lemma: $\exp(A)\exp(B) = \exp(A+B + \frac{1}{2}[A,B])$ when $[A, [A,B]] = 0$.
* **Epic B-04: The Kac-Moody Anomaly on the Budget**
  * Formalize normal-ordered density modes $\rho_{m} = \sum :c_{k+m}^\dagger c_k:$.
  * Prove the central extension: $[\rho_{-m}, \rho_n] \psi = m \delta_{mn} \psi$ for any state $\psi \in \mathcal{B}$ with adequate margin.

### Sprint 2: Vertex Algebras, Interactions & Duality
* **Epic B-05: The Sugawara Construction**
  * Prove exact quadratic decomposition of the free kinetic Hamiltonian in terms of density modes: $H_0 \psi = \frac{2\pi}{L} \sum m \rho_{-m}\rho_m \psi + E_{\mathrm{zero}} \psi$.
* **Epic B-06: Mattis-Mandelstam Formula on the Budget**
  * Construct vertex operators using Klein factors $F_\nu$ and Umbral phase fields $W^\pm(x)$.
  * Prove the operator equivalence on matrix elements.
* **Epic B-07: The Bogoliubov Transformation & T-Duality**
  * Diagonalize the density-density forward-scattering Hamiltonian algebraically ($v_1 > |v_2|$).
  * Formalize T-Duality as an `AlgEquiv` mapping $g \leftrightarrow 1/g$ and $O_{\mathrm{CDW}} \leftrightarrow O_{\mathrm{SC}}$.

---

## 4. Backlog: Advanced Phases (Preparing for Upstream Integration)

* **Phase VII: Inverse Mattis-Mandelstam & Refermionization (Chapters on Luther-Emery & Impurities):**
  * Construct dual CAR fermions directly from vertex operators.
  * Map the Sine-Gordon cosine interaction at $K=1/2$ to an exact massive Dirac fermion.
  * Formalize von Delft & Schoeller's finite-$L$ impurity decoupling and boundary Majorana zero mode.
* **Phase VIII: Non-Abelian Bosonization ($SU(2)_1$ Current Algebra):**
  * Non-Abelian spin currents $J^a_m$ with Lie-algebraic Kac-Moody commutators $[J^a_m, J^b_n] = i \epsilon^{abc} J^c_{m+n} + \frac{1}{2}m\delta_{m,-n}\delta^{ab}$.
  * Non-Abelian Sugawara construction and $SU(2)$ primary fields.

---

## 5. R&D Discovery & Failure Tracking

* A dedicated file `docs/LOG_DISCOVERY_AND_PIVOTS.md` records:
  1. Failed proof attempts (e.g., tactic timeouts with `ring` vs `simp`).
  2. Type-class obstructions (e.g., non-unital vs unital algebra representations).
  3. Strategic pivots (e.g., replacing irrational normalization factors $\frac{1}{\sqrt{2}}$ with integer currents $R^c, R^s$).
