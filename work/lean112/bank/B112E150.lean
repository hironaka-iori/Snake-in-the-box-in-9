import B112E150Part0001
namespace B112E150
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem constraints_unsat (p : Nat → Bool) (h : Constraints p) : False := by
  have hh := step523 p h
  contradiction
#print axioms constraints_unsat
end B112E150
