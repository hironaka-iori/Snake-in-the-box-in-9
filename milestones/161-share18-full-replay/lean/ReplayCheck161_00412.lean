import ReplayData161_0012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok412 : check start412 proof412 = true := by
  decide +kernel
#print axioms ok412
theorem ok413 : check start413 proof413 = true := by
  decide +kernel
#print axioms ok413
theorem ok414 : check start414 proof414 = true := by
  decide +kernel
#print axioms ok414
theorem ok415 : andB (check start415 proof415) (cpOk (replay start415 proof415) start416) = true := by
  decide +kernel
#print axioms ok415
end Snake9.ReplayFull161
