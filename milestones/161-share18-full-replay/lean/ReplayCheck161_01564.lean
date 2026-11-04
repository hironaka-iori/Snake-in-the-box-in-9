import ReplayData161_0048
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1564 : check start1564 proof1564 = true := by
  decide +kernel
#print axioms ok1564
theorem ok1565 : check start1565 proof1565 = true := by
  decide +kernel
#print axioms ok1565
theorem ok1566 : check start1566 proof1566 = true := by
  decide +kernel
#print axioms ok1566
theorem ok1567 : andB (check start1567 proof1567) (cpOk (replay start1567 proof1567) start1568) = true := by
  decide +kernel
#print axioms ok1567
end Snake9.ReplayFull161
