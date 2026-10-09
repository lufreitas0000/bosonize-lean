# Appendix A03 proposal: integer energies and filtered operator domains

## Arithmetic and basis subsets

Take a positive natural h and set L = 2h for half-filled chapters. The asymmetric band is `[-h+1,h]`; do not call it a reflection-symmetric set of integer representatives. It has exactly h occupied modes k ≤ 0.
Admissible charge sectors are strictly $-h \le N \le h$. Outside that range, the sector subspace is empty (dimension zero) and has no nonzero ground ket.

**Definition:** Define relative charge in ℤ, not by natural subtraction: `N(S) = (#S : ℤ) − h`. Define P(S) in ℤ. Define the ground-energy integer t(N) by the unique integer satisfying `2 t(N) = N(N+1)`, proving that the product is even. Then `e(S)=P(S)−t(N(S))` is an integer.
Define the diagonal relative-charge observable $\hat{N} \delta_S = N(S) \delta_S$ and excitation energy observable $\hat{E} \delta_S = e(S) \delta_S$ on the occupation basis.
For admissible $N$, the ground configuration is $S_N = \{k \in \Lambda^* \mid k \le N\}$, with ground ket $|N\rangle_0 = \delta_{S_N}$.

*Lean 4 Proof Strategy:* Use `Int` for `N`, `P(S)`, and `t(N)`. For `t(N)`, define it as `(N * (N + 1)) / 2`, and prove an auxiliary lemma `even_mul_succ (N : ℤ) : Even (N * (N + 1))` using `Int.Even`. The definition of `e(S)` then trivially lands in `ℤ`. No division issues since `2 ∣ N * (N + 1)`.

**Lemma:** Prove `e(S) ≥ 0` before converting it to a natural number. No rational or real division is needed in the combinatorial layer.

*Lean 4 Proof Strategy:* The proof `e(S) ≥ 0` should proceed by bounding `P(S)` below by the minimal sum of `#S` distinct integers from the band. Define `e_nat (S) : ℕ := e(S).toNat`. Auxiliary lemma: `P(S) ≥ t(N(S))`, which can be shown by summing the lowest possible `#S` occupied modes.

**Definition:** For sorted occupied modes $s_i$ indexed by $0 \le i < \#S$, the ground reference is $g_i = -h+1+i$.

*Lean 4 Proof Strategy:* Define this as a function `g : Fin (#S) → ℤ`, where `g i = -h + 1 + (i : ℤ)`.

**Lemma:** Prove reindexing of sums, strict monotonicity, `s_i ≥ g_i`, and `e(S)=Σ_i(s_i−g_i)`. The empty configuration must be covered. Derive nonnegative, nondecreasing displacements `d_i`; this extra monotonicity is needed for efficient frozen-margin proofs, beyond the loose bound `d_i ≤ K`. The ground configuration $S_N$ is the unique configuration with $e(S) = 0$ in sector $N$.

*Lean 4 Proof Strategy:* Use `Finset.sum` to relate `P(S)` to `Σ_i s_i`. Strict monotonicity of `s_i` gives `s_i ≥ g_i` by induction on `i`. Then `d_i = s_i - g_i` is non-negative and non-decreasing since `s_{i+1} - s_i ≥ 1` implies `d_{i+1} - d_i = s_{i+1} - s_i - 1 ≥ 0`. The sum formula `e(S) = Σ_i d_i` follows from linearity of summation and the arithmetic series formula for `Σ g_i`.

**Definition:** Distinguish fixed-charge budgets `B(N,K)`, fixed-energy spaces `H(N,E)`, and the charge-box budget `B(K,Nmax)`. Fixed-energy spaces with distinct $E$ are mutually orthogonal, while $B(N,K) = \bigoplus_{E=0}^K H(N,E)$ and $\mathcal{B}_{K,N_{\max}} = \bigoplus_{|N| \le N_{\max}} B(N,K)$ are nested direct sums of coordinate spans.
Label coordinate projections by their full data: $P_{N,K}$ on $B(N,K)$ and $P_{K,N_{\max}}$ on $\mathcal{B}_{K,N_{\max}}$. For multi-species systems, excitation cutoff is defined as the total excitation energy $\sum_\nu e_\nu(S_\nu) \le K$.

*Lean 4 Proof Strategy:* Use `Submodule.span ℂ` of the selected occupation basis vectors. Construct the coordinate projection using `Module.Basis.constr`, with identity on retained coordinates and zero elsewhere; prove its range and self-adjointness from the occupation basis.

**Theorem:** Prove the sector ground ket belongs to `B(N,K)` and is nonzero for every admissible `N`. At `K=0` the fixed-charge budget has dimension one: $H(N,0) = \mathbb{C} \cdot |N\rangle_0$. Do not require every anti-vacuity example to have dimension greater than one; use `K≥1` when proving an excited witness.

*Lean 4 Proof Strategy:* The ground ket corresponds to `s_i = g_i`, so `d_i = 0` and `e(S) = 0 ≤ K`. Thus it is in `B(N,K)`. For dimension one at `K=0`, prove that `e(S) = 0` implies `d_i = 0` for all `i` (since `d_i ≥ 0`), meaning the only configuration is the ground ket. For excited witness, construct a configuration with `d_{#S - 1} = 1`.

## Ambient action and budget maps

**Theorem:** An operator A of energy shift `d` and charge shift `q` (satisfying $[\hat{N}, A] = q A$) is an ambient linear map with a grading theorem. For `d≥0` it maps `B(N,K)` into `B(N+q,K+d)`, not generally into `B(N,K)`. For negative shifts, formulate output budgets using integer cutoffs, declaring negative-energy spaces zero, or split the case `K<|d|` and prove annihilation before taking natural subtraction. Charge preservation ($q=0$) must be an explicit hypothesis to keep the target sector $N$.

*Lean 4 Proof Strategy:* Formalize the energy shift as a graded module structure. Define `Shift A q d := ∀ (S), e(S) ≤ K → A(S) ∈ B(N+q, K+d)`. For `d < 0`, define the target budget bound as `max 0 (K+d)` or use `Int` for `K` until final extraction.

**Definition:** If compression is desired, define `A_{N,K} = P_{N,K} A P_{N,K}` explicitly. Ambient and compressed powers are different operations. The notation `A^j ψ` must identify which is used.

*Lean 4 Proof Strategy:* Define compressed operator `compress A K := (proj K) ∘ₗ A ∘ₗ (incl K)`. Ambient power is `A^j`, compressed power is `(compress A K)^j`.

**Theorem:** For polynomial creation of weight `m`, `C_m : F≤K → F≤(K+m)` is the natural typed map. Only `P_K C_m` is an endomorphism of `F≤K`. Its CCR has a boundary correction; a scalar CCR on all of the finite slice contradicts the trace theorem already proved in chapter 2.

*Lean 4 Proof Strategy:* Define the typed raising map and its compression explicitly. For the compressed annihilator/creator commutator `[A_m,C_n]`, expand the exact intermediate-projection remainder. A creator/creator commutator is not the scalar CCR under discussion. Retain the boundary term and use the trace no-go only with its nonzero-carrier and characteristic-zero premises.

## Composition theorem and margin accounting

If A=B only on a subspace V, the equality cannot automatically be substituted in A Cψ unless Cψ lies in V.

**Lemma:** Introduce a reusable lemma:
- C sends V into W;
- A and B agree on W;
- therefore AC and BC agree on V.

*Lean 4 Proof Strategy:* Let `V, W` be `Submodule`. Given `hc : ∀ v ∈ V, C v ∈ W` and `hab : ∀ w ∈ W, A w = B w`, prove `∀ v ∈ V, A (C v) = B (C v)`. In Lean: `theorem comp_agree {V W : Submodule ℂ X} (hc : MapsTo C V W) (hab : EqOn A B W) : EqOn (A ∘ C) (B ∘ C) V`.

**Definition:** For an operator word with shifts `d₁,…,d_r` in the actual right-to-left application order, define the maximum cumulative upward excursion. A conservative bound is the sum of positive shifts. Use `K` plus this excursion in every `M1/M2` check needed during a rewrite. An input-only margin is not a margin for the entire calculation.

*Lean 4 Proof Strategy:* List the shifts in actual application order, form all prefix sums with a scan starting at 0, and take their maximum with 0. The sum of positive shifts is a proved upper bound. Check the example `[2,-2]`, whose maximal excursion is 2; reversing that application-order list would incorrectly give 0 for this word. Recheck suffixes of rewritten words at each substitution.

**Lemma:** Projection must also be tracked. In general `P A P B P ≠ P A B P`; discarded intermediate states can return into the retained slice. This is exactly why projected creators acquire edge terms. Similarly, a restricted equality `(A−B)P=0` implies `P(A†−B†)=0`, not `(A†−B†)P=0`. Adjoint identities require their own source/target argument.

*Lean 4 Proof Strategy:* Prove the exact difference `P A B P − P A P B P = P A (1−P) B P`. A nonzero value of this remainder on a selected vector proves inequality; merely knowing A or B fails to commute with P is insufficient. For the adjoint, take adjoints of the restricted equality, reverse factors, and use P†=P.

## Uniform mode cutoffs

**Definition:** Introduce an independent mode cutoff `M`. The natural conservative uniform condition for all pairwise density commutators of modes `|m|,|n|≤M` on the input budget is
\[
 2M+K+N_{max}\le h.
\]

*Lean 4 Proof Strategy:* Simply define this as a Prop: `def UniformCutoff (M K N_max h : ℕ) : Prop := 2 * M + K + N_max ≤ h`.

The chapter formulas summing `m=1,…,h−1` do not satisfy this uniformly when `h` is large. Repeated products require replacing `K` by the intermediate-energy bound as well.

**Lemma:** Algebraic vanishing of a lowering mode `m>K` does not imply that a raising mode `m>K` vanishes; it maps out of the budget and is often nonzero.

*Lean 4 Proof Strategy:* Prove that `Lowering m` on `B(N, K)` is zero when `m > K` (since energy cannot be negative), but `Raising m` can be a valid injection into `B(N, K+m)`. Therefore, applying `P_K` makes it vanish as an endomorphism, but it is not algebraically zero on the ambient space.

The constants in sharper R1/R2 proofs should be derived from the actual word being commuted, rather than adding a guessed strengthening everywhere. Record these dependencies before freezing a theorem.

*Coordinate energy convention:* Here P(S) means the vacuum-subtracted momentum energy `Σ k∈S, k − EΩ`, with `EΩ=−h(h−1)/2`. Then the sector ground has P=t(N), including empty/full admissible sectors. Do not confuse this scalar with bare `Σ k∈S, k`. A restricted commutator identity already proved on its input needs no extra same-budget premise on its two intermediate products.
