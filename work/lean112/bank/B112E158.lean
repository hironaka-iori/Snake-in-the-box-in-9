import B112E158Part0073
namespace B112E158
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem constraints_unsat (p : Nat → Bool) (h : Constraints p) : False := by
  have hh := step6266 p h
  contradiction
#print axioms constraints_unsat
end B112E158
