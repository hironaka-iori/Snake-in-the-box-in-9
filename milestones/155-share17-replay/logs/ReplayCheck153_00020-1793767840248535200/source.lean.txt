import ReplayData153_0000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (andB)
open Snake9.LratFast153Replay
theorem ok20 : check start20 proof20 = true := by
  decide +kernel
#print axioms ok20
theorem ok21 : check start21 proof21 = true := by
  decide +kernel
#print axioms ok21
theorem ok22 : check start22 proof22 = true := by
  decide +kernel
#print axioms ok22
theorem ok23 : check start23 proof23 = true := by
  decide +kernel
#print axioms ok23
end Snake9.ReplayFull153
