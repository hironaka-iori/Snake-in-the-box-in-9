import ContractedExample237_0
import ContractedExample237_1
import ContractedExample237_2
import ContractedExample237_3
import ContractedExample237_4
import ContractedExample237_5
import ContractedExample237_6
import ContractedExample237_7

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

namespace ContractedDegrees237

private theorem example_range_blocks :
    List.range 512 =
      List.range' 0 64 ++
      List.range' 64 64 ++
      List.range' 128 64 ++
      List.range' 192 64 ++
      List.range' 256 64 ++
      List.range' 320 64 ++
      List.range' 384 64 ++
      List.range' 448 64 := by
  decide

/-- Complete two-neighbour label table on the nine-dimensional cube. -/
theorem example_label_table :
    ((List.range 512).filterMap fun z =>
      match cubeNeighboursInExample z with
      | [a, b] => some (z, a, b)
      | _ => none) =
    [(2,3,10), (7,3,23), (8,9,10), (21,17,23), (26,10,27), (31,23,27)] := by
  let f := fun z : Nat =>
    match cubeNeighboursInExample z with
    | [a, b] => some (z, a, b)
    | _ => none
  change (List.range 512).filterMap f =
    [(2,3,10), (7,3,23), (8,9,10), (21,17,23), (26,10,27), (31,23,27)]
  have h0 : (List.range' 0 64).filterMap f =
      [(2,3,10), (7,3,23), (8,9,10), (21,17,23), (26,10,27), (31,23,27)] :=
    example_rows_0
  have h1 : (List.range' 64 64).filterMap f = [] := example_rows_1
  have h2 : (List.range' 128 64).filterMap f = [] := example_rows_2
  have h3 : (List.range' 192 64).filterMap f = [] := example_rows_3
  have h4 : (List.range' 256 64).filterMap f = [] := example_rows_4
  have h5 : (List.range' 320 64).filterMap f = [] := example_rows_5
  have h6 : (List.range' 384 64).filterMap f = [] := example_rows_6
  have h7 : (List.range' 448 64).filterMap f = [] := example_rows_7
  rw [example_range_blocks]
  simp only [List.filterMap_append, h0, h1, h2, h3, h4, h5, h6, h7,
    List.append_nil, List.nil_append]

#print axioms example_label_table

end ContractedDegrees237
