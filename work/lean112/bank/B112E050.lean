import B112E050Part0142
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem constraints_unsat (p : Nat → Bool) (h : Constraints p) : False := by
  have hh := step10906 p h
  contradiction
#print axioms constraints_unsat
end B112E050
