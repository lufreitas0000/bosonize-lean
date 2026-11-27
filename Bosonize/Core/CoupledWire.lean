module

public import Bosonize.Core.CoupledWire.DualityMatrix
public import Bosonize.Core.CoupledWire.DualityBoundary
public import Bosonize.Core.CoupledWire.DiracMass
public import Bosonize.Core.CoupledWire.SSHZeroModes
public import Bosonize.Core.CoupledWire.BlochDiracAndGauge
public import Bosonize.Core.CoupledWire.GaugeAndConductivity
public import Bosonize.Core.CoupledWire.TPfaffianThreeCone
public import Bosonize.Core.CoupledWire.QED3Duality
public import Bosonize.Core.CoupledWire.N2BosonicTI

/-!
# 2D Coupled-Wire Bosonization & Fermion–Boson Duality (MAM `arXiv:1510.08455`)

Thin barrel module aggregating the 9 modular Mathlib4-native coupled-wire duality submodules
consolidated from `xxz-benchmark/lean/XXZBenchmark/` under `QMB-P1B-04b`:
1. `DualityMatrix` — `D`, `P`, `A`, `D^2 = I`, `D P D^T = -P`, `D A D^T = -A`, odd-`N` obstruction;
2. `DualityBoundary` — `Δ`, `S`, OBC/PBC duality defects, and charge conservation;
3. `DiracMass` — staggered Dirac mass `D^T M = -M`, 4-wire `Δ^T S`, alternating-mass duality;
4. `SSHZeroModes` — exact finite-`N` SSH edge zero modes, residual scaling, and tunnel splitting;
5. `BlochDiracAndGauge` — `2×2` Bloch Dirac matrix on `GaussianInt`, symmetries, `K_MAM`, kinetic cancel;
6. `GaugeAndConductivity` — staggered CS, `(T,X,N)` mutual-CS gauge invariance, `π`-mode Schur, Dirac-CFL;
7. `TPfaffianThreeCone` — universal `det_fromBlocks_scalar_diag`, 6-wire 3-cone, Fu–Kane ↔ `T`-Pfaffian;
8. `QED3Duality` — `N = 1` QED₃ bilinears, universal `transProj`, and irreducible conductivity duality;
9. `N2BosonicTI` — finite-`2m` Klein-factor commutator algebra, `K = σ^x`, and `{T, C, I, M, R}`.
-/
