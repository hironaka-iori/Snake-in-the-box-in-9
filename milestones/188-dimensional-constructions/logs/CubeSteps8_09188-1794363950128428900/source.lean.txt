import CubeData8188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness8
theorem steps9 : ∀ j : Fin 7,
  (pathVertex ⟨63+j.val+1,by omega⟩).val =
  Nat.xor (pathVertex ⟨63+j.val,by omega⟩).val (2^transitions[63+j.val]!) := by decide +kernel
#print axioms steps9
end Dimensional188.Witness8
