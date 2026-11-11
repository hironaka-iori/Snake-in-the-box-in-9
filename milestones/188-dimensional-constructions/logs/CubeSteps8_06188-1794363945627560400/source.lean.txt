import CubeData8188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness8
theorem steps6 : ∀ j : Fin 7,
  (pathVertex ⟨42+j.val+1,by omega⟩).val =
  Nat.xor (pathVertex ⟨42+j.val,by omega⟩).val (2^transitions[42+j.val]!) := by decide +kernel
#print axioms steps6
end Dimensional188.Witness8
