import CubeInverseBase237

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

namespace CubeInverse

theorem kernel_case_10 (x : Vertex 5) :
    flipSum 9 (fun y => coefficient (weight 9 y)) (true, (false, (true, (false, x)))) =
      spike 9 (true, (false, (true, (false, x)))) := by
  have h : every 5 (fun z =>
      flipSum 9 (fun y => coefficient (weight 9 y)) (true, (false, (true, (false, z)))) ==
        spike 9 (true, (false, (true, (false, z))))) = true := by decide
  exact beq_iff_eq.mp (of_every _ _ h x)

#print axioms kernel_case_10

end CubeInverse
