import CubeData8188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness8
theorem rows24 : ∀ i : Fin 3, Row ⟨96+i.val,by omega⟩ := by
  unfold Row
  decide +kernel
#print axioms rows24
end Dimensional188.Witness8
