import ReplayData161_0038
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1244 : check start1244 proof1244 = true := by
  decide +kernel
#print axioms ok1244
theorem ok1245 : check start1245 proof1245 = true := by
  decide +kernel
#print axioms ok1245
theorem ok1246 : check start1246 proof1246 = true := by
  decide +kernel
#print axioms ok1246
theorem ok1247 : andB (check start1247 proof1247) (cpOk (replay start1247 proof1247) start1248) = true := by
  decide +kernel
#print axioms ok1247
end Snake9.ReplayFull161
