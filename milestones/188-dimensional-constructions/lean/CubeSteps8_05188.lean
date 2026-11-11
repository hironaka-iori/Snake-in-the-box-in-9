import CubeData8188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness8
theorem steps5 : ∀ j : Fin 7,
  (pathVertex ⟨35+j.val+1,by omega⟩).val =
  Nat.xor (pathVertex ⟨35+j.val,by omega⟩).val (2^transitions[35+j.val]!) := by decide +kernel
#print axioms steps5
end Dimensional188.Witness8
