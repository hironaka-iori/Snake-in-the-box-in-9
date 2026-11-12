import LowerData194
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Lower194
theorem oldRows2 : ∀ i : Fin 8, oldRow ⟨16+i.val,by omega⟩ := by
  unfold oldRow
  decide +kernel
#print axioms oldRows2
theorem newRows2 : ∀ i : Fin 8, newRow ⟨16+i.val,by omega⟩ := by
  unfold newRow
  decide +kernel
#print axioms newRows2
end Lower194
