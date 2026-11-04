import ReplayData153_0008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (andB)
open Snake9.LratFast153Replay
theorem ok284 : check start284 proof284 = true := by
  decide +kernel
#print axioms ok284
theorem ok285 : check start285 proof285 = true := by
  decide +kernel
#print axioms ok285
theorem ok286 : check start286 proof286 = true := by
  decide +kernel
#print axioms ok286
theorem ok287 : andB (check start287 proof287) (cpOk (replay start287 proof287) start288) = true := by
  decide +kernel
#print axioms ok287
end Snake9.ReplayFull153
