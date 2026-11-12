import LowerData194
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Lower194
theorem oldRows1 : ∀ i : Fin 8, oldRow ⟨8+i.val,by omega⟩ := by
  unfold oldRow
  decide +kernel
#print axioms oldRows1
theorem newRows1 : ∀ i : Fin 8, newRow ⟨8+i.val,by omega⟩ := by
  unfold newRow
  decide +kernel
#print axioms newRows1
end Lower194
