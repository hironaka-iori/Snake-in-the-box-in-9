import ReplayData161_0039
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1276 : check start1276 proof1276 = true := by
  decide +kernel
#print axioms ok1276
theorem ok1277 : check start1277 proof1277 = true := by
  decide +kernel
#print axioms ok1277
theorem ok1278 : check start1278 proof1278 = true := by
  decide +kernel
#print axioms ok1278
theorem ok1279 : andB (check start1279 proof1279) (cpOk (replay start1279 proof1279) start1280) = true := by
  decide +kernel
#print axioms ok1279
end Snake9.ReplayFull161
