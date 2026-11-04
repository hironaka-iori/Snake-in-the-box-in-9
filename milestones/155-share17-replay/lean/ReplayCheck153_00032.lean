import ReplayData153_0001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (andB)
open Snake9.LratFast153Replay
theorem ok32 : check start32 proof32 = true := by
  decide +kernel
#print axioms ok32
theorem ok33 : check start33 proof33 = true := by
  decide +kernel
#print axioms ok33
theorem ok34 : check start34 proof34 = true := by
  decide +kernel
#print axioms ok34
theorem ok35 : check start35 proof35 = true := by
  decide +kernel
#print axioms ok35
end Snake9.ReplayFull153
