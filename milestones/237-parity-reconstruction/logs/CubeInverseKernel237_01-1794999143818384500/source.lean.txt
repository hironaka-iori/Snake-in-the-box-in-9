import CubeInverseBase237

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

namespace CubeInverse

theorem kernel_case_01 (x : Vertex 5) :
    flipSum 9 (fun y => coefficient (weight 9 y)) (false, (false, (false, (true, x)))) =
      spike 9 (false, (false, (false, (true, x)))) := by
  have h : every 5 (fun z =>
      flipSum 9 (fun y => coefficient (weight 9 y)) (false, (false, (false, (true, z)))) ==
        spike 9 (false, (false, (false, (true, z))))) = true := by decide
  exact beq_iff_eq.mp (of_every _ _ h x)

#print axioms kernel_case_01

end CubeInverse
