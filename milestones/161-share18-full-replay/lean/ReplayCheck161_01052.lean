import ReplayData161_0032
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok1052 : check start1052 proof1052 = true := by
  decide +kernel
#print axioms ok1052
theorem ok1053 : check start1053 proof1053 = true := by
  decide +kernel
#print axioms ok1053
theorem ok1054 : check start1054 proof1054 = true := by
  decide +kernel
#print axioms ok1054
theorem ok1055 : andB (check start1055 proof1055) (cpOk (replay start1055 proof1055) start1056) = true := by
  decide +kernel
#print axioms ok1055
end Snake9.ReplayFull161
