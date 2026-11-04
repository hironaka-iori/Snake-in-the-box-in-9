import ReplayData161_0049
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1596 : check start1596 proof1596 = true := by
  decide +kernel
#print axioms ok1596
theorem ok1597 : check start1597 proof1597 = true := by
  decide +kernel
#print axioms ok1597
theorem ok1598 : check start1598 proof1598 = true := by
  decide +kernel
#print axioms ok1598
theorem ok1599 : andB (check start1599 proof1599) (cpOk (replay start1599 proof1599) start1600) = true := by
  decide +kernel
#print axioms ok1599
end Snake9.ReplayFull161
