import ReplayData161_0043
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1404 : check start1404 proof1404 = true := by
  decide +kernel
#print axioms ok1404
theorem ok1405 : check start1405 proof1405 = true := by
  decide +kernel
#print axioms ok1405
theorem ok1406 : check start1406 proof1406 = true := by
  decide +kernel
#print axioms ok1406
theorem ok1407 : andB (check start1407 proof1407) (cpOk (replay start1407 proof1407) start1408) = true := by
  decide +kernel
#print axioms ok1407
end Snake9.ReplayFull161
