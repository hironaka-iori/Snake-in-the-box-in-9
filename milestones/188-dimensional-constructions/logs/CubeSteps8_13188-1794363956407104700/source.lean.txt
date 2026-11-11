import CubeData8188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness8
theorem steps13 : ∀ j : Fin 7,
  (pathVertex ⟨91+j.val+1,by omega⟩).val =
  Nat.xor (pathVertex ⟨91+j.val,by omega⟩).val (2^transitions[91+j.val]!) := by decide +kernel
#print axioms steps13
end Dimensional188.Witness8
