import B112E047Part0066
namespace B112E047
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem constraints_unsat (p : Nat → Bool) (h : Constraints p) : False := by
  have hh := step5827 p h
  contradiction
#print axioms constraints_unsat
end B112E047
