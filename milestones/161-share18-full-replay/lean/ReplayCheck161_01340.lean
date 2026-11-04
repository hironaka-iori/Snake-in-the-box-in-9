import ReplayData161_0041
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1340 : check start1340 proof1340 = true := by
  decide +kernel
#print axioms ok1340
theorem ok1341 : check start1341 proof1341 = true := by
  decide +kernel
#print axioms ok1341
theorem ok1342 : check start1342 proof1342 = true := by
  decide +kernel
#print axioms ok1342
theorem ok1343 : andB (check start1343 proof1343) (cpOk (replay start1343 proof1343) start1344) = true := by
  decide +kernel
#print axioms ok1343
end Snake9.ReplayFull161
