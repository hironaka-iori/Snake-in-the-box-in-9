import ReplayData161_0040
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1308 : check start1308 proof1308 = true := by
  decide +kernel
#print axioms ok1308
theorem ok1309 : check start1309 proof1309 = true := by
  decide +kernel
#print axioms ok1309
theorem ok1310 : check start1310 proof1310 = true := by
  decide +kernel
#print axioms ok1310
theorem ok1311 : andB (check start1311 proof1311) (cpOk (replay start1311 proof1311) start1312) = true := by
  decide +kernel
#print axioms ok1311
end Snake9.ReplayFull161
