import ReplayData161_0035
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1148 : check start1148 proof1148 = true := by
  decide +kernel
#print axioms ok1148
theorem ok1149 : check start1149 proof1149 = true := by
  decide +kernel
#print axioms ok1149
theorem ok1150 : check start1150 proof1150 = true := by
  decide +kernel
#print axioms ok1150
theorem ok1151 : andB (check start1151 proof1151) (cpOk (replay start1151 proof1151) start1152) = true := by
  decide +kernel
#print axioms ok1151
end Snake9.ReplayFull161
