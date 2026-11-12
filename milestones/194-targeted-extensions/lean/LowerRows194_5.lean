import LowerData194
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Lower194
theorem oldRows5 : ∀ i : Fin 8, oldRow ⟨40+i.val,by omega⟩ := by
  unfold oldRow
  decide +kernel
#print axioms oldRows5
theorem newRows5 : ∀ i : Fin 8, newRow ⟨40+i.val,by omega⟩ := by
  unfold newRow
  decide +kernel
#print axioms newRows5
end Lower194
