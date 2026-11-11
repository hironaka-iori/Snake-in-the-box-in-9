import CubeData8188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness8
theorem steps10 : ∀ j : Fin 7,
  (pathVertex ⟨70+j.val+1,by omega⟩).val =
  Nat.xor (pathVertex ⟨70+j.val,by omega⟩).val (2^transitions[70+j.val]!) := by decide +kernel
#print axioms steps10
end Dimensional188.Witness8
