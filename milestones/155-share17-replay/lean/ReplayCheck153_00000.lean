import ReplayData153_0000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (andB)
open Snake9.LratFast153Replay
theorem ok0 : check start0 proof0 = true := by
  decide +kernel
#print axioms ok0
theorem ok1 : check start1 proof1 = true := by
  decide +kernel
#print axioms ok1
theorem ok2 : check start2 proof2 = true := by
  decide +kernel
#print axioms ok2
theorem ok3 : check start3 proof3 = true := by
  decide +kernel
#print axioms ok3
end Snake9.ReplayFull153
