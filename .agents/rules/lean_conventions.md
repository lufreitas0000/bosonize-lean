# Lean 4 Coding Conventions and Project Rules

## 1. Mathematical Strictness
* **Exact Algebraic Scope:** Every formalized statement must represent an exact identity between finite-dimensional or purely algebraic objects. Algebraic polynomial operators are permitted without asserting analytical boundedness or a Hilbert completion. Do not substitute analytical limits or topological approximations (`≈`) for exact identities.
* **Explicit Hypotheses:** Regime conditions (e.g., energy budget margins $K$, $N$, $m$) must be explicit statement hypotheses. Do not hide them.
* **Typed Restricted Action:** Track map sources/targets, operator order, adjoints, and projection remainders. Attach margins to the inputs where an identity is used; distinguish useful local conditions from stronger sufficient wrappers. Consult `.agents/skills/formalizer/references/proof_design.md` for the relevant mathematical contracts.

## 2. Naming Conventions
* **Theorems/Lemmas:** Use `snake_case` (e.g., `card_lattice_band`, `umbral_heisenberg`). These are opaque proofs.
* **Definitions/Data:** Use `lowerCamelCase` (e.g., `bandFinset`, `discreteDeriv`). These are computable functions or data.
* **Types/Classes/Namespaces:** Use `UpperCamelCase` (e.g., `LambdaDual`, `Bosonize.Core`).

## 3. Anti-Vacuity (No Green-Washing)
* Never define an operator, set, or physical state as trivially `0`, `id`, `∅`, or `⊥` just to satisfy a theorem.
* Ensure key objects ship with non-degeneracy/witness lemmas to prove that the constrained subspaces (e.g., the energy budget) are physically satisfiable and not empty.
* Where a claim uses a positive state, inverse map, or nonzero leakage action, establish that object's existence or the required coefficient. Nonempty budgets alone do not supply this evidence. Label proposed witness stubs separately from proved results.

## 4. The Single-Sorry Contract (Staging)
* Files in `BosonizeStubs/` must contain completely elaborated `def` and `abbrev` blocks.
* In Phase A, theorem and lemma signatures in `BosonizeStubs/` must terminate with exactly one `:= by sorry`. During authorized Phase B work, replace only their proof bodies with complete proofs. Do not leave trailing or intermediate `sorry` tokens inside partial definitions.

## 5. Core Completeness
* Files migrated to `Bosonize/Core/` must compile with zero warnings and zero `sorry` or `admit` tokens.
* Resolve warnings at their cause; do not suppress linters or lower warning thresholds for promotion. Use `omit` for unused section assumptions where appropriate. A change to a locked signature/context follows the interface-review procedure; existing Core stays frozen.
* The `#print axioms` output for any theorem must only reveal standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
* Complete Core sources, including proof bodies, are frozen by `scripts/guards/core_lock.py` against `docs/spec/core_locks.json`. CI and `make lock-check` run this guard as well as the v2 definition/statement guard. Never alter an existing Core source or its approved hash to solve downstream proof problems.

## 6. Approved Interface Preservation
* Run `python3 scripts/guards/stub_lock.py --check --strict` before and after Phase B proof batches. Never run `--update` to bypass a failed check; baseline changes require exact independent review under `.agents/skills/formalizer/references/pipeline.md`; only substantive ambiguity requires a human decision.
* Preserve approved definitions, abbreviations, instances, declaration names, namespaces, hypotheses, and conclusions. The v2 guard freezes these commands and lemma headers in the guarded files. It does not freeze imported dependencies or toolchain state: review source and dependency diffs separately. A matching hash does not certify mathematical correctness or complete proofs.
* CI runs the guard tests and strict freeze verification before building. New declarations/files need independent review and a scoped committed baseline under the automatic pipeline. Use an approved `--baseline-ref` (or CI variable `STUB_LOCK_BASELINE_REF`) to verify against a committed baseline rather than trusting a modified working-tree lock.

## 7. Critical Use of Suggestions
* Consult chapter-relevant `docs/stub_suggestion/` files when drafting interfaces and `docs/proof_suggestion/` files when planning and implementing proofs.
* Read chapter-relevant `notes/appendices/` and reconcile applicable review corrections with current source versions. Statements and sketches in the notes also require scrutiny; report false or underspecified claims instead of treating source prose as proof.
* Suggestions are unverified advisory material. Compare them with the reconciled source, check all hypotheses and non-vacuity conditions, and validate adopted code with the installed Lean compiler. Reject changes that weaken a claim, hide a domain restriction, or alter a frozen definition merely to accommodate a suggested proof.
* Record suggestion paths and adopted, adapted, or rejected ideas with reasons in the companion notebook.

## 8. Modular Library Architecture & PhysLean / Mathlib4 Standards
* **Domain-Modular Core vs. Chapter Re-Exports:** Organize reusable Lean library code by mathematical structure and physical domain (e.g. `Algebra/`, `Graph/`, `Spin/`, `Fermion/`, `Models/Heisenberg/`, `Models/Hubbard/`, `Spectral/`) rather than locking definitions inside monolithic textbook-chapter files. Maintain textbook/note traceability through a **Thin Chapter Certification Layer** (`Chapters/` or `Tasaki/`) that imports the domain modules and re-exports or aliases the chapter's named theorems alongside companion notes/blueprints.
* **`Defs.lean` / `Basic.lean` / Proof Splitting & File Size Limits:** Keep Lean files compact ($200\text{--}500$ lines). Isolate types, structures, and definitions with minimal imports in `Defs.lean`, foundational simp lemmas and instances in `Basic.lean`, and heavy proofs in dedicated theorem modules so downstream consumers only import `Defs.lean` or `Basic.lean`.
* **Typeclasses (`class`) vs. Structures (`structure`):** Use `class` only for canonical, unique mathematical structures on a type or property-only predicates (e.g. `IsBipartite`). Use explicit `structure` records for parameterized physical models, Hamiltonians, and coupling configurations to avoid typeclass search loops and instance diamonds.
* **Dual-Agent Top-Down / Bottom-Up Clean-Room Workflow:**
  1. **Top-Down Specification Agent (Phase A):** Translates pedagogical notes (`notes/md/`) into formal target signatures, explicit hypotheses, and computable non-vacuity witnesses in the chapter certification/staging layer.
  2. **Bottom-Up Library Agent (Phase B):** Develops general, reusable domain lemmas (`Algebra/`, `Spectral/`, `Spin/`, `Fermion/`) from the leaves up, discharging the locked top-down chapter theorems via modular composition.

## 9. Architectural Blueprints & Implementation Review Directives
Before implementing Part I Chapter 4 (Marshall-Lieb-Mattis), Part I Chapter 5 (Lieb-Schultz-Mattis), or Sprint 1B (CAR & Jordan-Wigner), agents **must read** the architectural review blueprints in `notes/reviews/`:
1. **Marshall-Lieb-Mattis Theorem (Part I Chapter 4):**
   * **Document:** `notes/reviews/Marshall_Lieb_Mattis_Lean4_Implementation_Strategy.md`.
   * **Discrete Marshall Phase:** Define $p_B(\sigma) = (-1)^{N_B^\downarrow(\sigma)}$ by sublattice spin parity on configurations $\sigma : \Lambda \to \mathrm{Bool}$ without matrix exponentials.
   * **Rectangular Intertwiner:** Frame commutation as $\widetilde{H}_{k+1} L_k = L_k \widetilde{H}_k$ where $L = \sum_{i \in A} S_i^- - \sum_{j \in B} S_j^-$.
   * **Combinatorial Sign-Change Lemma (W):** Prove that for any strictly positive vector $\psi \in \Omega_k$ ($k < n$), $(L_k \psi)(\tau_A) > 0 > (L_k \psi)(\tau_B)$ on the extreme boundary configurations $\tau_A$ (all down in $A$) and $\tau_B$ (all down in $B$). This establishes that $L_k \psi$ changes sign and contradicts Perron-Frobenius positivity in $\Omega_{k+1}$, confining the ground state to $k = n$ ($M = 0$).
   * **Singlet Certificate:** Conclude $S_{\mathrm{tot}} = 0$ via Casimir $C = (S_{\mathrm{tot}}^z)^2 - S_{\mathrm{tot}}^z + S_{\mathrm{tot}}^+ S_{\mathrm{tot}}^-$ annihilated by $\psi_0$ without requiring continuous $SU(2)$ representation theory.
2. **Lieb-Schultz-Mattis Theorem (Part I Chapter 5):**
   * **Document:** `notes/reviews/LSM_Lean4_Formalization_Strategy.md`.
   * **Configuration-First Diagonal Twist:** Represent states as `Config L → ℂ` with `Config L := Fin L → Fin 2`. Treat the twist as diagonal phase multiplication $u(\sigma) = \exp(i \frac{2\pi}{L} W(\sigma))$ avoiding `Matrix.exp`.
   * **Coefficient Action Convention:** The cyclic translation operator action on coefficients must follow $(T \psi)(\sigma) = \psi(\tau^{-1} \sigma)$. Reversing this inverts the translation-twist sign.
   * **Weighted Magnetization Algebra:** Prove the reindexing identity for $W(\tau \sigma) = \sum_j j m_j(\tau \sigma)$ over $\mathbb{R}$ before exponentiating.
   * **Orthogonality & Gap Bound:** Conclude $T (U \Phi_0) = - \lambda_0 (U \Phi_0)$, giving strict orthogonality $\langle \Phi_0 | U \Phi_0 \rangle = 0$. Evaluate the Rayleigh-Ritz gap bound $\Delta_L \le 2\pi^2 J / L$ via local bond flips.
3. **CAR, Jordan-Wigner & Kitaev Wire (Sprint 1B):**
   * **Document:** `notes/reviews/Sprint_1B_CAR_Jordan_Wigner_Majorana_Lean4_Strategy.md`.
   * **Two-Layer Architecture:** Abstract CAR algebra for symbolic zero-mode commutation ($H_{\mathrm{sweet}} = i t \sum_j b_j a_{j+1}$) + concrete constructive Jordan-Wigner realization on `Fin L → Bool`.
   * **JW String Parity:** Standardize on $K_j = \prod_{k < j} (-\sigma_k^z)$ to avoid staggered $(-1)^j$ discrepancies.
   * **Open-Chain Boundary:** Use typed chain `Fin (n + 1)` with bonds `Fin n` via `j.castSucc` and `j.succ` without periodic modular arithmetic.
4. **Quantum Mermin–Wagner Theorem (Part I Chapter 8):**
   * **Documents:** `notes/reviews/quantum_mermin_wagner_lean4_agent_strategy.md` and `notes/reviews/mermin_wagner_infrared_mathlib_agent_spec.md`.
   * **Algebraic Duhamel Inner Product:** Define $(A, B)_\beta$ purely algebraically over finite spectral decomposition $H = \sum_n E_n |n\rangle\langle n|$, bypassing continuous $\tau$-integrals.
   * **Square Shell Decomposition:** Partition non-zero momentum modes into square shells with exact cardinality $8r$, and bound dispersion via Mathlib's `Real.one_sub_sq_div_two_le_cos`.
   * **Harmonic Lower Bound:** Prove $\sum_{k \ne 0} \frac{1}{\omega(k)} \ge \frac{1}{\pi^2} H_{\lfloor L/4 \rfloor} \ge \frac{1}{2\pi^2} \ln L$ using Mathlib's `log_add_one_le_harmonic`.
   * **Field-Scaling Guard:** Do not state a uniform bound for fixed $h > 0$. Frame the physical theorem for $0 < h \le J/L^2$ or as the zero-field limit $\lim_{h \downarrow 0} \limsup_{L \to \infty} |m_L(h)| = 0$.
5. **AKLT Model & Exact 4-Fold Boundary Degeneracy (Part II Chapters 1 & 2):**
   * **Documents:** `notes/reviews/AKLT_Lean4_Exact_Boundary_Degeneracy_Implementation_Strategy.md` and `notes/reviews/AKLT_Lean4_Word_Reduction_and_Exact_Edge_Degeneracy_Agent_Spec.md`.
   * **Rational Spin-2 Projector ($P_2 \in \mathbb{Q}^{9 \times 9}$):** Define $P_2$ via 5 unnormalized orthogonal rational vectors without $\sqrt{2}$ factors. Prove $P_2^2 = P_2$, $P_2^T = P_2$, and $\operatorname{rank} P_2 = 5$ by finite rational arithmetic.
   * **Normal Words & Invertible Evaluation:** Evaluate the 4 boundary MPS states on the 4 normal words $\mathcal{N}_L = \{0^L, +0^{L-1}, -0^{L-1}, +-0^{L-2}\}$ (NOT words containing $++$ or $--$, which have zero amplitude).
   * **5-Constraint Word Reduction ($\dim \le 4$):** Prove the upper bound $\dim \ker H_L \le 4$ by reducing any zero-energy amplitude function to the 4 normal words using the 5 local bond relations, proving $\dim \ker H_L = 4$ for all open chains with $L \ge 2$.
6. **Kennedy–Tasaki Transformation & Transmuted Locality (Part II Chapter 3):**
   * **Documents:** `notes/reviews/kennedy_tasaki_lean4_agent_strategy.md` and `notes/reviews/kennedy_tasaki_locality_aklt_lean4_agent_packet.md`.
   * **Controlled-Rotation Representation:** Represent $U_L = \prod_{a < b} C_{ab}$ with $C_{ab} = (I - Q_a) + Q_a R_b^x$ on spin-1 configurations.
   * **Locality & External String Cancellation:** Prove that external string gates cancel against their adjoints due to the simultaneous $\pi$-rotation symmetry of the AKLT bond projector $[P_{j, j+1}^{(2)}, R_j^\alpha R_{j+1}^\alpha] = 0$.
   * **Transformed Projector on $\mathbb{Q}^9$:** The transformed bond is strictly local: $U_L P_{j, j+1}^{(2)} U_L = \operatorname{embed}_{j, j+1}(P_{\mathrm{KT}})$ with rational $9 \times 9$ matrix $P_{\mathrm{KT}} = C P^{(2)} C$.
   * **String Transmutation Sign:** Account for the exact raw open-chain relation $U_L O_{j, k}^z U_L = - S_j^z S_k^z$ (raw correlation $-4/9$ vs. physical string order $+4/9$).

---

## 10. The 3-Tier R&D Laboratory Protocol (`FiniteQMBLab` $\to$ `FiniteQMBStubs` $\to$ `FiniteQMB`)

To reconcile the exploratory nature of mathematical physics R&D with zero-sorry, cryptographically locked production standards, all formalization adheres to a **3-Tier Architecture**:

1. **Tier 1 — Unlocked R&D Laboratory (`FiniteQMBLab/`):**
   * **Permissive Sandbox:** Allows `sorry`, unused variables, trial definitions, and alternative/suboptimal proof strategies.
   * **Zero CI Interference:** Compiled via `make build-lab` (`lake build FiniteQMBLab`). Decoupled from `make ci` and `stub_lock.py` so active experiments never fail CI.
   * **Living Knowledge Archive (`FiniteQMBLab/Archive/`):** Not a dead graveyard; houses verified computable toy models ($N=2, 3, 4$), rigorous counterexamples, and documented dead-ends/obstructions. Every archived file is tracked in `FiniteQMBLab/Archive/INDEX.md`.
   * **Mandatory Structured Header:** Every lab file must begin with:
     ```lean
     /-!
     # Experiment: <Title>
     * Target Module / Topic: <Module or Review Note>
     * Hypothesis / Question: <What is being tested?>
     * Status: [CONFIRMED | COUNTEREXAMPLE | DEAD-END | SUBOPTIMAL-INFORMATIVE]
     * Date: YYYY-MM-DD
     * Author / Agent Role: <Scout Agent / Adversarial Agent / Human>
     * Key Takeaways: <What was learned>
     * Promotion Target: <Path in FiniteQMB/ if promoted, or NONE>
     -/
     ```

2. **Tier 2 — Formal Staging Gate (`FiniteQMBStubs/`):**
   * Cleaned, standardized theorem contracts staged in `FiniteQMBStubs/<Domain>/<Topic>.lean` ending with `:= by sorry`.
   * Cryptographically frozen by `stub_locks.v2.json` and audited with `python3 scripts/guards/stub_lock.py --check --strict`.
   * Executed via Phase B clean-room agents in isolated sandboxes.

3. **Tier 3 — Production Codebase (`FiniteQMB/`):**
   * **Layer 1 (Modular Domain Library):** Concept-indexed, PhysLean/Mathlib4 standard, zero-`sorry`, `-DwarningAsError=true`.
   * **Layer 2 (Chapter Certification):** Thin certification files (`FiniteQMB/Chapters/PartXXChYY.lean`) mapping 1-to-1 to LaTeX book chapters with computable physical witnesses. Layer 2 imports Layer 1; Layer 1 NEVER imports Layer 2.

4. **Agent Roles in the Lab:**
   * **Scout / Experimenter Agent:** Explores alternative proofs, tests review claims, builds small $N=2,3,4$ models.
   * **Adversarial / Falsification Agent:** Actively seeks edge-case singularities, counterexamples, and sign frustrations.
   * **Promotion Agent:** Moves verified definitions to Layer 1, contracts to Tier 2, and indexes findings in `FiniteQMBLab/Archive/INDEX.md`.

