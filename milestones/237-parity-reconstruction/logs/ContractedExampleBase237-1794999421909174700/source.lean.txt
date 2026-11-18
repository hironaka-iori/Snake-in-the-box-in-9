import Std

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

namespace ContractedDegrees237

def exampleVertices : List Nat := [3, 9, 10, 17, 23, 27]

def cubeNeighboursInExample (z : Nat) : List Nat :=
  exampleVertices.filter fun x =>
    [1, 2, 4, 8, 16, 32, 64, 128, 256].contains (Nat.xor x z)


end ContractedDegrees237
