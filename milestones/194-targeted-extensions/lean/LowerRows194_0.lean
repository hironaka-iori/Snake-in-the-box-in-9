import LowerData194
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Lower194
theorem oldRows0 : ∀ i : Fin 8, oldRow ⟨0+i.val,by omega⟩ := by
  unfold oldRow
  decide +kernel
#print axioms oldRows0
theorem newRows0 : ∀ i : Fin 8, newRow ⟨0+i.val,by omega⟩ := by
  unfold newRow
  decide +kernel
#print axioms newRows0
end Lower194
