import ReplayData161_0031
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1000 : check start1000 proof1000 = true := by
  decide +kernel
#print axioms ok1000
theorem ok1001 : check start1001 proof1001 = true := by
  decide +kernel
#print axioms ok1001
theorem ok1002 : check start1002 proof1002 = true := by
  decide +kernel
#print axioms ok1002
theorem ok1003 : check start1003 proof1003 = true := by
  decide +kernel
#print axioms ok1003
end Snake9.ReplayFull161
