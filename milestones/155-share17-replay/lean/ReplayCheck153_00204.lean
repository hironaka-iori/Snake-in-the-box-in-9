import ReplayData153_0006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (andB)
open Snake9.LratFast153Replay
theorem ok204 : check start204 proof204 = true := by
  decide +kernel
#print axioms ok204
theorem ok205 : check start205 proof205 = true := by
  decide +kernel
#print axioms ok205
theorem ok206 : check start206 proof206 = true := by
  decide +kernel
#print axioms ok206
theorem ok207 : check start207 proof207 = true := by
  decide +kernel
#print axioms ok207
end Snake9.ReplayFull153
