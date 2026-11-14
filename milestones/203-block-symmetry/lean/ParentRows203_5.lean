import ParentData203
namespace ParentRows203_5
open ParentData203
set_option maxRecDepth 100000
theorem rows : ∀ i : Fin 1, ∀ j : Fin 51, i.val+5<51 → pairProperty (i.val+5) j.val := by
  decide +kernel
#print axioms rows
end ParentRows203_5
