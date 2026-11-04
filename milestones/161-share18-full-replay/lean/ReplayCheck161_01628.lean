import ReplayData161_0050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1628 : check start1628 proof1628 = true := by
  decide +kernel
#print axioms ok1628
theorem ok1629 : check start1629 proof1629 = true := by
  decide +kernel
#print axioms ok1629
theorem ok1630 : check start1630 proof1630 = true := by
  decide +kernel
#print axioms ok1630
theorem ok1631 : andB (check start1631 proof1631) (cpOk (replay start1631 proof1631) start1632) = true := by
  decide +kernel
#print axioms ok1631
end Snake9.ReplayFull161
