import ReplayData161_0029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok956 : check start956 proof956 = true := by
  decide +kernel
#print axioms ok956
theorem ok957 : check start957 proof957 = true := by
  decide +kernel
#print axioms ok957
theorem ok958 : check start958 proof958 = true := by
  decide +kernel
#print axioms ok958
theorem ok959 : andB (check start959 proof959) (cpOk (replay start959 proof959) start960) = true := by
  decide +kernel
#print axioms ok959
end Snake9.ReplayFull161
