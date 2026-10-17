import B112E256Part0171
namespace B112E256
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem constraints_unsat (p : Nat → Bool) (h : Constraints p) : False := by
  have hh := step12803 p h
  contradiction
#print axioms constraints_unsat
end B112E256
