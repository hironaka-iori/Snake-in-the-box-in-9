import ContractedExampleBase237

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

namespace ContractedDegrees237

theorem example_rows_0 :
    ((List.range' 0 64).filterMap fun z =>
      match cubeNeighboursInExample z with
      | [a, b] => some (z, a, b)
      | _ => none) =
    [(2,3,10), (7,3,23), (8,9,10), (21,17,23), (26,10,27), (31,23,27)] := by
  decide

#print axioms example_rows_0

end ContractedDegrees237
