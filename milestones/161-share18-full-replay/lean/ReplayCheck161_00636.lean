import ReplayData161_0019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok636 : check start636 proof636 = true := by
  decide +kernel
#print axioms ok636
theorem ok637 : check start637 proof637 = true := by
  decide +kernel
#print axioms ok637
theorem ok638 : check start638 proof638 = true := by
  decide +kernel
#print axioms ok638
theorem ok639 : andB (check start639 proof639) (cpOk (replay start639 proof639) start640) = true := by
  decide +kernel
#print axioms ok639
end Snake9.ReplayFull161
