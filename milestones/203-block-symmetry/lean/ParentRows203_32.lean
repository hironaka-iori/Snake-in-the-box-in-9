import ParentData203
namespace ParentRows203_32
open ParentData203
set_option maxRecDepth 100000
theorem rows : ∀ i : Fin 1, ∀ j : Fin 51, i.val+32<51 → pairProperty (i.val+32) j.val := by
  decide +kernel
#print axioms rows
end ParentRows203_32
