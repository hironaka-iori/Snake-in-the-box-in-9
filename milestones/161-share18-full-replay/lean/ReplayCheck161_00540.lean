import ReplayData161_0016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok540 : check start540 proof540 = true := by
  decide +kernel
#print axioms ok540
theorem ok541 : check start541 proof541 = true := by
  decide +kernel
#print axioms ok541
theorem ok542 : check start542 proof542 = true := by
  decide +kernel
#print axioms ok542
theorem ok543 : andB (check start543 proof543) (cpOk (replay start543 proof543) start544) = true := by
  decide +kernel
#print axioms ok543
end Snake9.ReplayFull161
