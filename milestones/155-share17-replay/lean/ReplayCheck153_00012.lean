import ReplayData153_0000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (andB)
open Snake9.LratFast153Replay
theorem ok12 : check start12 proof12 = true := by
  decide +kernel
#print axioms ok12
theorem ok13 : check start13 proof13 = true := by
  decide +kernel
#print axioms ok13
theorem ok14 : check start14 proof14 = true := by
  decide +kernel
#print axioms ok14
theorem ok15 : check start15 proof15 = true := by
  decide +kernel
#print axioms ok15
end Snake9.ReplayFull153
