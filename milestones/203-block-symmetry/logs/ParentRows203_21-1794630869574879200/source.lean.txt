import ParentData203
namespace ParentRows203_21
open ParentData203
set_option maxRecDepth 100000
theorem rows : ∀ i : Fin 1, ∀ j : Fin 51, i.val+21<51 → pairProperty (i.val+21) j.val := by
  decide +kernel
#print axioms rows
end ParentRows203_21
