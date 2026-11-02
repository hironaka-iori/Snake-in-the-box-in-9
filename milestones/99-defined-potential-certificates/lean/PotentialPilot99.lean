import FastDiagram99
import CompletedPotential99
import ConditionalPotential99
import PotentialAssembly98

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Potential99
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78

def edgeTest (floor : Nat → Nat) (P : Nat) (pi : Nat → Nat)
    (di q c : Nat) : Bool :=
  !fastKeep di q c || decide
    (P + pi (edgeTarget q di c) ≤ weight floor q di c + pi (edgeSource q di c))

theorem completed_chunk :
    (List.range 216).all (fun k =>
      edgeTest completedCredit 483 Completed.potential 35 0 (11448+k)) = true := by
  decide +kernel

theorem conditional_chunk :
    (List.range 216).all (fun k =>
      edgeTest conditionalCredit 496 Conditional.potential 177 43 (11448+k)) = true := by
  decide +kernel

#print axioms completed_chunk
#print axioms conditional_chunk
end Snake9.Potential99
