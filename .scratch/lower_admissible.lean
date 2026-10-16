import Bosonize.Core.Ch14Mandelstam
import Bosonize.Core.Ch16FieldHamiltonian
open Bosonize
namespace LowerAdm
 def w : Fin 2 → ℤ := fun _ => 0
example : A05.admissible 2 (Ch13.lowerCharge w 1) := by
  intro ν
  fin_cases ν <;> simp [Ch07.admissible, Ch13.lowerCharge, w, Function.update]
end LowerAdm
