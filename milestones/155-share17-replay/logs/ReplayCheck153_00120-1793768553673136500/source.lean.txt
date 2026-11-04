import ReplayData153_0003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (andB)
open Snake9.LratFast153Replay
theorem ok120 : check start120 proof120 = true := by
  decide +kernel
#print axioms ok120
theorem ok121 : check start121 proof121 = true := by
  decide +kernel
#print axioms ok121
theorem ok122 : check start122 proof122 = true := by
  decide +kernel
#print axioms ok122
theorem ok123 : check start123 proof123 = true := by
  decide +kernel
#print axioms ok123
end Snake9.ReplayFull153
