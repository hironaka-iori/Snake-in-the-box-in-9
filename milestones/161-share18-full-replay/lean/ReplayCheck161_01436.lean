import ReplayData161_0044
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1436 : check start1436 proof1436 = true := by
  decide +kernel
#print axioms ok1436
theorem ok1437 : check start1437 proof1437 = true := by
  decide +kernel
#print axioms ok1437
theorem ok1438 : check start1438 proof1438 = true := by
  decide +kernel
#print axioms ok1438
theorem ok1439 : andB (check start1439 proof1439) (cpOk (replay start1439 proof1439) start1440) = true := by
  decide +kernel
#print axioms ok1439
end Snake9.ReplayFull161
