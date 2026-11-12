import LowerData194
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Lower194
theorem oldRows3 : ∀ i : Fin 8, oldRow ⟨24+i.val,by omega⟩ := by
  unfold oldRow
  decide +kernel
#print axioms oldRows3
theorem newRows3 : ∀ i : Fin 8, newRow ⟨24+i.val,by omega⟩ := by
  unfold newRow
  decide +kernel
#print axioms newRows3
end Lower194
