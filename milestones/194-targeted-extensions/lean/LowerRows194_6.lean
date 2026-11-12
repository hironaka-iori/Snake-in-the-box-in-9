import LowerData194
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Lower194
theorem oldRows6 : ∀ i : Fin 1, oldRow ⟨48+i.val,by omega⟩ := by
  unfold oldRow
  decide +kernel
#print axioms oldRows6
theorem newRows6 : ∀ i : Fin 2, newRow ⟨48+i.val,by omega⟩ := by
  unfold newRow
  decide +kernel
#print axioms newRows6
end Lower194
