import Bosonize.Core.Ch14Mandelstam
import Bosonize.Core.Ch16FieldHamiltonian
open scoped BigOperators Classical
open Bosonize
namespace BandMembership
noncomputable local instance modeOrd (h : ℕ) : LinearOrder (A05.Mode (Fin 2) h) := A05.speciesOrder h
noncomputable local instance modeDecEq (h : ℕ) : DecidableEq (A05.Mode (Fin 2) h) := A05.localModeDecidableEq h
abbrev mn : Ch01.Band 4 := ⟨-1, by norm_num [Ch01.inBandPredicate]⟩
abbrev m0 : Ch01.Band 4 := ⟨0, by norm_num [Ch01.inBandPredicate]⟩
abbrev m1 : Ch01.Band 4 := ⟨1, by norm_num [Ch01.inBandPredicate]⟩
abbrev m2 : Ch01.Band 4 := ⟨2, by norm_num [Ch01.inBandPredicate]⟩
def w : Fin 2 → ℤ := fun _ => 0
lemma ground_mem (x : Ch01.Band 4) : (1,x) ∈ A05.groundConfiguration 2 w ↔ x.val ≤ 0 := by
  simp only [A05.groundConfiguration, A05.jointConfiguration, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, Ch07.groundConfiguration, Finset.mem_filter]
  simp [w]
example (x : Ch01.Band 4) (hx : x.val = -1) : (1,x) ∈ A05.groundConfiguration 2 w := by
  rw [ground_mem]
  omega
example (x : Ch01.Band 4) (hx : x.val = 0) : (1,x) ∈ A05.groundConfiguration 2 w := by
  rw [ground_mem]
  omega
example (x : Ch01.Band 4) (hx : x.val = 1) : (1,x) ∉ A05.groundConfiguration 2 w := by
  rw [ground_mem]
  omega
example (x : Ch01.Band 4) (hx : x.val = 2) : (1,x) ∉ A05.groundConfiguration 2 w := by
  rw [ground_mem]
  omega
end BandMembership
namespace BandMembership
example (x : Ch01.Band 4) : ((1,x) ∈ A05.groundConfiguration 2 w) ↔ x.val ≤ 0 := by
  rw [ground_mem]
end BandMembership
