import ReplayData161_0021
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (andB)
open Snake9.LratFast144
theorem ok700 : check start700 proof700 = true := by
  decide +kernel
#print axioms ok700
theorem ok701 : check start701 proof701 = true := by
  decide +kernel
#print axioms ok701
theorem ok702 : check start702 proof702 = true := by
  decide +kernel
#print axioms ok702
theorem ok703 : andB (check start703 proof703) (cpOk (replay start703 proof703) start704) = true := by
  decide +kernel
#print axioms ok703
end Snake9.ReplayFull161
