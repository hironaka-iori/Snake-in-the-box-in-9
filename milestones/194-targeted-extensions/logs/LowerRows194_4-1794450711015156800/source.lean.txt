import LowerData194
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Lower194
theorem oldRows4 : ∀ i : Fin 8, oldRow ⟨32+i.val,by omega⟩ := by
  unfold oldRow
  decide +kernel
#print axioms oldRows4
theorem newRows4 : ∀ i : Fin 8, newRow ⟨32+i.val,by omega⟩ := by
  unfold newRow
  decide +kernel
#print axioms newRows4
end Lower194
