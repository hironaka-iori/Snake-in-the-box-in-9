import ReplayData161_0033
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1084 : check start1084 proof1084 = true := by
  decide +kernel
#print axioms ok1084
theorem ok1085 : check start1085 proof1085 = true := by
  decide +kernel
#print axioms ok1085
theorem ok1086 : check start1086 proof1086 = true := by
  decide +kernel
#print axioms ok1086
theorem ok1087 : andB (check start1087 proof1087) (cpOk (replay start1087 proof1087) start1088) = true := by
  decide +kernel
#print axioms ok1087
end Snake9.ReplayFull161
