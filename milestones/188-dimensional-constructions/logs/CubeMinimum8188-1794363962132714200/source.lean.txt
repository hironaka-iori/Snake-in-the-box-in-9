import CubeData8188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness8
theorem minimum_crossings : ∀ k : Fin 8, 4 ≤ transitions.toList.count k.val := by decide +kernel
#print axioms minimum_crossings
end Dimensional188.Witness8
