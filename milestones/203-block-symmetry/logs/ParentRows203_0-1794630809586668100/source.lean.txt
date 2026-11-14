import ParentData203
namespace ParentRows203_0
open ParentData203
set_option maxRecDepth 100000
theorem rows : ∀ i : Fin 1, ∀ j : Fin 51, i.val+0<51 → pairProperty (i.val+0) j.val := by
  decide +kernel
#print axioms rows
end ParentRows203_0
