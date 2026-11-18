---
title: "Independent CH21 Umklapp Witness & Counterexample Derivation"
phase: Phase B
milestone: V1-S9
status: active
owner: lufreitas0000
last_updated: "2026-11-18"
tags: [bosonize-lean, v1-s9, ch21]
depends_on:
  - docs/plans/v1-s9/ch21_api_reconciliation.md
  - notes/md/ch21_spinful_models.md
  - notes/appendices/a09_duality_spin_and_umklapp.md
---

# Independent CH21 Umklapp Witness & Counterexample Derivation

**Date:** 2026-11-18  
**Milestone:** V1-S9 / CH21 Phase B (`BosonizeStubs/Ch21SpinfulModels.lean`)

---

## 1. Setup & Conventions (`Fin 4` Multi-Species Fock Space)

Let `h : ℕ` with `0 < h`, and set `L := 2 * h`.
1. **Band (`Bosonize.Ch01.Band (2 * h)`):** Integer momenta `k : ℤ` satisfying `-h < k ≤ h`, i.e., `k ∈ {1 - h, 2 - h, ..., 0, 1, ..., h}` (total `2 * h` modes).
2. **Species Order (`Fin 4`):** Canonical linear order `0 < 1 < 2 < 3`, corresponding to:
   - `0 = L↑` (left-moving spin-up)
   - `1 = L↓` (left-moving spin-down)
   - `2 = R↑` (right-moving spin-up)
   - `3 = R↓` (right-moving spin-down)
   - Mode pairs `(ν, k)` are ordered lexicographically: `(ν₁, k₁) < (ν₂, k₂)` iff `ν₁ < ν₂` or `(ν₁ = ν₂ ∧ k₁ < k₂)`.
3. **CAR Action Sign (`Bosonize.Ch04` & `Bosonize.A05`):** For mode `m = (ν, k)` and joint occupation `S`, both `A05.creation h ν k` and `A05.annihilation h ν k` carry the Jordan-Wigner parity factor `(-1 : ℂ) ^ precedingCount (ν, k) S`, where:
   `precedingCount (ν, k) S = (∑ η < ν, (speciesConfiguration h S η).card) + Ch04.precedingCount k (speciesConfiguration h S ν)`.
4. **Position Fields & Twists (`A05.liftedAnnihilation` at `periodicTwist (2 * h)`):**
   - `c_ν(x) := A05.liftedAnnihilation h (fun _ => Ch06Ext.periodicTwist (2 * h)) ν x = (1 / √(2 * h)) • ∑_k ζ^(k * x) • A05.annihilation h ν k`, where `ζ := A01.canonicalRoot (2 * h)` is a primitive `(2 * h)`-th root of unity (`ζ^(2 * h) = 1`, `|ζ| = 1`).
   - `c†_ν(x) := LinearMap.adjoint (c_ν(x)) = (1 / √(2 * h)) • ∑_k ζ^(-k * x) • A05.creation h ν k`.
5. **Umklapp Operator (`Fin (2 * h)`, matching `Ch01.Lattice (2 * h)` for `h > 0`):**
   $$H_U(g_U) := \frac{g_U}{2h} \sum_{x \in \mathrm{Fin}(2h)} \Big( c^\dagger_{L\uparrow}(x)\, c^\dagger_{L\downarrow}(x)\, c_{R\downarrow}(x)\, c_{R\uparrow}(x) + c^\dagger_{R\uparrow}(x)\, c^\dagger_{R\downarrow}(x)\, c_{L\downarrow}(x)\, c_{L\uparrow}(x) \Big).$$

---

## 2. Exact Zero-Charge Witness Derivation (`-g_U / (2h)^2`)

Consider the zero-charge ground vacuum `|Ω₀⟩ := A05.groundKet h (fun _ => 0) = A02.ket S₀`, where every species `ν ∈ Fin 4` occupies `Ch07.groundConfiguration h 0 = {1 - h, ..., 0}` (`h` occupied modes).

Define the target occupation configuration `S_target` by species:
- Species `0` (`L↑`): `Ch07.groundConfiguration h 1 = {1 - h, ..., 0, 1}` (`h + 1` modes; relative charge `+1`).
- Species `1` (`L↓`): `Ch07.groundConfiguration h 1 = {1 - h, ..., 0, 1}` (`h + 1` modes; relative charge `+1`).
- Species `2` (`R↑`): `(Ch07.groundConfiguration h 0).erase (1 - h) = {2 - h, ..., 0}` (`h - 1` modes; relative charge `-1`).
- Species `3` (`R↓`): `(Ch07.groundConfiguration h 0).erase (1 - h) = {2 - h, ..., 0}` (`h - 1` modes; relative charge `-1`).

Set `|Ψ_target⟩ := A02.ket S_target`. Notice `|Ψ_target⟩` has total charge `(+1) + (+1) + (-1) + (-1) = 0`, while its species charge tuple `(+1, +1, -1, -1)` differs from `(0, 0, 0, 0)`.

### Step 2.1: Charge-Sector Filtering
- The `+ h.c.` conjugate term `c†_{R↑} c†_{R↓} c_{L↓} c_{L↑}` shifts `(N_{L↑}, N_{L↓}, N_{R↑}, N_{R↓})` from `(0, 0, 0, 0)` to `(-1, -1, +1, +1)`.
- By distinct-sector orthogonality with `(+1, +1, -1, -1)`, `⟨Ψ_target | H_U^{(h.c.)} | Ω₀⟩ = 0` identically.

### Step 2.2: Uniqueness of Momentum Tuple `(k₀, k₁, k₃, k₂)`
Evaluating `⟨Ψ_target | c†_{0,k₀} c†_{1,k₁} c_{3,k₃} c_{2,k₂} | Ω₀⟩`:
- Species `2` transitions from `{1 - h, ..., 0}` to `{2 - h, ..., 0}` via `c_{2,k₂}`, uniquely forcing `k₂ = 1 - h`.
- Species `3` transitions from `{1 - h, ..., 0}` to `{2 - h, ..., 0}` via `c_{3,k₃}`, uniquely forcing `k₃ = 1 - h`.
- Species `1` transitions from `{1 - h, ..., 0}` to `{1 - h, ..., 0, 1}` via `c†_{1,k₁}`, uniquely forcing `k₁ = 1`.
- Species `0` transitions from `{1 - h, ..., 0}` to `{1 - h, ..., 0, 1}` via `c†_{0,k₀}`, uniquely forcing `k₀ = 1`.

Every quadruple `(k₀, k₁, k₃, k₂) ≠ (1, 1, 1 - h, 1 - h)` produces an occupation distinct from `S_target` (or annihilates `|Ω₀⟩`), hence has inner product `0`. Notice that for all `h ≥ 1`, both `1 ∈ Band (2 * h)` (since `-h < 1 ≤ h`) and `1 - h ∈ Band (2 * h)` (since `-h < 1 - h ≤ h`).

### Step 2.3: Jordan-Wigner Preceding Counts & Sign (`8h - 1`)
Apply `c†_{(0, 1)} c†_{(1, 1)} c_{(3, 1-h)} c_{(2, 1-h)}` right-to-left starting on `S₀`:
1. **`c_{(2, 1-h)}` on `S₀`:**
   - Species `0` has `h` occupied modes; species `1` has `h` occupied modes.
   - Inside species `2`, `1 - h` is the minimum of `Band (2 * h)`, so `0` modes lie strictly below `1 - h`.
   - Preceding count `p₁ = h + h + 0 = 2h`. Leaves `S₁ = S₀.erase (2, 1 - h)`.
2. **`c_{(3, 1-h)}` on `S₁`:**
   - Species `0` has `h` modes; species `1` has `h` modes; species `2` now has `h - 1` modes.
   - Inside species `3`, `0` modes lie strictly below `1 - h`.
   - Preceding count `p₂ = h + h + (h - 1) + 0 = 3h - 1`. Leaves `S₂ = S₁.erase (3, 1 - h)`.
3. **`c†_{(1, 1)}` on `S₂`:**
   - Species `0` has `h` modes; species `1` has `{1 - h, ..., 0}` (`h` modes, all `< 1`).
   - Preceding count `p₃ = h + h = 2h`. Leaves `S₃ = insert (1, 1) S₂`.
4. **`c†_{(0, 1)}` on `S₃`:**
   - Species `0` has `{1 - h, ..., 0}` (`h` modes, all `< 1`).
   - Preceding count `p₄ = h`. Leaves `S₄ = insert (0, 1) S₃ = S_target`.

Sum of preceding counts:
$$p_1 + p_2 + p_3 + p_4 = 2h + (3h - 1) + 2h + h = 8h - 1.$$
Because `8h - 1 = 2(4h - 1) + 1` is odd for all `h ≥ 1`, the CAR sign is identically:
$$(-1)^{8h - 1} = -1.$$

### Step 2.4: Fourier Phase & Spatial Contraction
For `(k₀, k₁, k₃, k₂) = (1, 1, 1 - h, 1 - h)` at lattice site `x : Fin (2 * h)` (`≃ Ch01.Lattice (2 * h)` for `h > 0`):
- Four `normalization (2 * h)` factors yield `(1 / √(2 * h))⁴ = (2 * h)^{-2}`.
- Product of character phases:
  $$\zeta^{-k_0 x} \cdot \zeta^{-k_1 x} \cdot \zeta^{k_3 x} \cdot \zeta^{k_2 x} = \zeta^{(-1 - 1 + (1 - h) + (1 - h))x} = \zeta^{-2h x} = (\zeta^{2h})^{-x} = 1^{-x} = 1.$$
- Summing `2 * h` identical site contributions (`Fintype.card (Fin (2 * h)) = 2 * h`) and multiplying by `g_U / (2 * h)`:
$$\langle \Psi_{\mathrm{target}} \mid H_U(g_U) \mid \Omega_0 \rangle = \frac{g_U}{2h} \cdot (2h) \cdot \frac{1}{(2h)^2} \cdot (-1) = -\frac{g_U}{(2h)^2}.$$

### Step 2.5: Concrete Checks (`h = 1` and `h = 2`)
- **`h = 1` (`L = 2`), `g_U = 1`:** `-1 / (2 * 1)² = -1 / 4`.
  Here `1 - h = 0`, `S_target` on species `2, 3` is `∅ = groundConfiguration 1 (-1)`, so `|Ψ_target⟩` equals `A05.groundKet 1 (1, 1, -1, -1)` (excitation energy `0`).
- **`h = 2` (`L = 4`), `g_U = 1`:** `-1 / (2 * 2)² = -1 / 16`.

---

## 3. `h = 2, L = 4` Ground-to-Ground Selection Rule & Non-Invariance Counterexample

At `h = 2` (`L = 4`), `Band 4 = {-1, 0, 1, 2}` and `groundConfiguration 2 0 = {-1, 0}`:
1. **Vanishing of Ground-to-Ground Umklapp:**
   Transitioning to `A05.groundKet 2 (1, 1, -1, -1)` requires species `0, 1` to occupy `{-1, 0, 1}` (`k₀ = k₁ = 1`) and species `2, 3` to occupy `groundConfiguration 2 (-1) = {-1}` (`k₂ = k₃ = 0`). The lattice sum becomes:
   $$\sum_{x = 0}^{3} \zeta^{(-1 - 1 + 0 + 0)x} = \sum_{x = 0}^{3} (-1)^x = 1 - 1 + 1 - 1 = 0.$$
   Hence the ground-to-ground amplitude vanishes identically, and Umklapp scattering out of `|Ω₀⟩` necessarily populates particle-hole holes at `1 - h = -1` (producing `{0}` in species `2, 3`, excitation energy `h - 1 = 1` per hole, total excitation energy `2(h - 1) = 2`).
2. **Non-Invariance of Budgets & Low-Energy Charge-Boxes Containing `|Ω₀⟩`:**
   For `g_U ≠ 0`, `⟨Ψ_target | H_U(g_U) | Ω₀⟩ = -g_U / (2h)² ≠ 0`. Since `|Ω₀⟩ ∈ A05.jointBudget h (fun _ => 0) 0` while `|Ψ_target⟩` has charges `(+1, +1, -1, -1)` (orthogonal to `A05.jointBudget h (fun _ => 0) K` for EVERY `K`) and excitation energy `2 * (h - 1)` above the `(+1, +1, -1, -1)` ground state, no fixed-`Ns` budget centered at `Ns = 0` — and at `h = 2`, no low-energy `K ≤ 1` charge-box containing `|Ω₀⟩` — is invariant under `H_U(g_U)` (by contrast, Pauli-blocked extreme sectors such as `Ns = (+2, +2, +2, +2)` at `h = 2` are trivially annihilated by `H_U`). This witnesses why bosonizing Umklapp around `|Ω₀⟩` requires tracking charge-shift sectors `Ns + (+1, +1, -1, -1)` and excitation energy headroom `≥ 2(h - 1)`.
