import CubeData8188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness8
theorem rows15 : ∀ i : Fin 4, Row ⟨60+i.val,by omega⟩ := by
  unfold Row
  decide +kernel
#print axioms rows15
end Dimensional188.Witness8
