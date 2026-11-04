import ReplayData161_0042
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1372 : check start1372 proof1372 = true := by
  decide +kernel
#print axioms ok1372
theorem ok1373 : check start1373 proof1373 = true := by
  decide +kernel
#print axioms ok1373
theorem ok1374 : check start1374 proof1374 = true := by
  decide +kernel
#print axioms ok1374
theorem ok1375 : andB (check start1375 proof1375) (cpOk (replay start1375 proof1375) start1376) = true := by
  decide +kernel
#print axioms ok1375
end Snake9.ReplayFull161
