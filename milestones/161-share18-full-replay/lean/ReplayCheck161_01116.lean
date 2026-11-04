import ReplayData161_0034
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1116 : check start1116 proof1116 = true := by
  decide +kernel
#print axioms ok1116
theorem ok1117 : check start1117 proof1117 = true := by
  decide +kernel
#print axioms ok1117
theorem ok1118 : check start1118 proof1118 = true := by
  decide +kernel
#print axioms ok1118
theorem ok1119 : andB (check start1119 proof1119) (cpOk (replay start1119 proof1119) start1120) = true := by
  decide +kernel
#print axioms ok1119
end Snake9.ReplayFull161
