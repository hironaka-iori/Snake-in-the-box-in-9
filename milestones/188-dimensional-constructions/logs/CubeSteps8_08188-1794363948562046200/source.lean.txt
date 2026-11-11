import CubeData8188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness8
theorem steps8 : ∀ j : Fin 7,
  (pathVertex ⟨56+j.val+1,by omega⟩).val =
  Nat.xor (pathVertex ⟨56+j.val,by omega⟩).val (2^transitions[56+j.val]!) := by decide +kernel
#print axioms steps8
end Dimensional188.Witness8
