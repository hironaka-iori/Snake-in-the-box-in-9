import B112E057Part0139
namespace B112E057
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem constraints_unsat (p : Nat → Bool) (h : Constraints p) : False := by
  have hh := step10949 p h
  contradiction
#print axioms constraints_unsat
end B112E057
