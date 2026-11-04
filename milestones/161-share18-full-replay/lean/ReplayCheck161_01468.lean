import ReplayData161_0045
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1468 : check start1468 proof1468 = true := by
  decide +kernel
#print axioms ok1468
theorem ok1469 : check start1469 proof1469 = true := by
  decide +kernel
#print axioms ok1469
theorem ok1470 : check start1470 proof1470 = true := by
  decide +kernel
#print axioms ok1470
theorem ok1471 : andB (check start1471 proof1471) (cpOk (replay start1471 proof1471) start1472) = true := by
  decide +kernel
#print axioms ok1471
end Snake9.ReplayFull161
