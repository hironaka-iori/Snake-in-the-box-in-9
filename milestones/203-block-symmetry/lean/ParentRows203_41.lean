import ParentData203
namespace ParentRows203_41
open ParentData203
set_option maxRecDepth 100000
theorem rows : ∀ i : Fin 1, ∀ j : Fin 51, i.val+41<51 → pairProperty (i.val+41) j.val := by
  decide +kernel
#print axioms rows
end ParentRows203_41
