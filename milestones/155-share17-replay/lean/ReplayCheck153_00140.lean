import ReplayData153_0004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (andB)
open Snake9.LratFast153Replay
theorem ok140 : check start140 proof140 = true := by
  decide +kernel
#print axioms ok140
theorem ok141 : check start141 proof141 = true := by
  decide +kernel
#print axioms ok141
theorem ok142 : check start142 proof142 = true := by
  decide +kernel
#print axioms ok142
theorem ok143 : check start143 proof143 = true := by
  decide +kernel
#print axioms ok143
end Snake9.ReplayFull153
