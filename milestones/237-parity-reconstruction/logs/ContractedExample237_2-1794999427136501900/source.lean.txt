import ContractedExampleBase237

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

namespace ContractedDegrees237

theorem example_rows_2 :
    ((List.range' 128 64).filterMap fun z =>
      match cubeNeighboursInExample z with
      | [a, b] => some (z, a, b)
      | _ => none) =
    [] := by
  decide

#print axioms example_rows_2

end ContractedDegrees237
