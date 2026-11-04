import ReplayData161_0037
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1212 : check start1212 proof1212 = true := by
  decide +kernel
#print axioms ok1212
theorem ok1213 : check start1213 proof1213 = true := by
  decide +kernel
#print axioms ok1213
theorem ok1214 : check start1214 proof1214 = true := by
  decide +kernel
#print axioms ok1214
theorem ok1215 : andB (check start1215 proof1215) (cpOk (replay start1215 proof1215) start1216) = true := by
  decide +kernel
#print axioms ok1215
end Snake9.ReplayFull161
