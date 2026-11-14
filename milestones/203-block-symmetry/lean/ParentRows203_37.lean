import ParentData203
namespace ParentRows203_37
open ParentData203
set_option maxRecDepth 100000
theorem rows : ∀ i : Fin 1, ∀ j : Fin 51, i.val+37<51 → pairProperty (i.val+37) j.val := by
  decide +kernel
#print axioms rows
end ParentRows203_37
