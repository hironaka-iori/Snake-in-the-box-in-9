import ParentData203
namespace ParentRows203_2
open ParentData203
set_option maxRecDepth 100000
theorem rows : ∀ i : Fin 1, ∀ j : Fin 51, i.val+2<51 → pairProperty (i.val+2) j.val := by
  decide +kernel
#print axioms rows
end ParentRows203_2
