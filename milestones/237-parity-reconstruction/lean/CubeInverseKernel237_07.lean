import CubeInverseBase237

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

namespace CubeInverse

theorem kernel_case_07 (x : Vertex 5) :
    flipSum 9 (fun y => coefficient (weight 9 y)) (false, (true, (true, (true, x)))) =
      spike 9 (false, (true, (true, (true, x)))) := by
  have h : every 5 (fun z =>
      flipSum 9 (fun y => coefficient (weight 9 y)) (false, (true, (true, (true, z)))) ==
        spike 9 (false, (true, (true, (true, z))))) = true := by decide
  exact beq_iff_eq.mp (of_every _ _ h x)

#print axioms kernel_case_07

end CubeInverse
