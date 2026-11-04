import ReplayData161_0036
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1180 : check start1180 proof1180 = true := by
  decide +kernel
#print axioms ok1180
theorem ok1181 : check start1181 proof1181 = true := by
  decide +kernel
#print axioms ok1181
theorem ok1182 : check start1182 proof1182 = true := by
  decide +kernel
#print axioms ok1182
theorem ok1183 : andB (check start1183 proof1183) (cpOk (replay start1183 proof1183) start1184) = true := by
  decide +kernel
#print axioms ok1183
end Snake9.ReplayFull161
