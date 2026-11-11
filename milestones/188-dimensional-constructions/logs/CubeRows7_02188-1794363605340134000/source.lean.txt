import CubeData7188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness7
theorem rows2 : ∀ i : Fin 8, Row ⟨16+i.val,by omega⟩ := by
  unfold Row
  decide +kernel
#print axioms rows2
end Dimensional188.Witness7
