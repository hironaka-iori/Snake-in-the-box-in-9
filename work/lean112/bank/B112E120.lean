import B112E120Part0010
namespace B112E120
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem constraints_unsat (p : Nat → Bool) (h : Constraints p) : False := by
  have hh := step1489 p h
  contradiction
#print axioms constraints_unsat
end B112E120
