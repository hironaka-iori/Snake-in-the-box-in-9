import CubeData7188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness7
theorem rows1 : ∀ i : Fin 8, Row ⟨8+i.val,by omega⟩ := by
  unfold Row
  decide +kernel
#print axioms rows1
end Dimensional188.Witness7
