import B112E153Part0087
namespace B112E153
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem constraints_unsat (p : Nat → Bool) (h : Constraints p) : False := by
  have hh := step7141 p h
  contradiction
#print axioms constraints_unsat
end B112E153
