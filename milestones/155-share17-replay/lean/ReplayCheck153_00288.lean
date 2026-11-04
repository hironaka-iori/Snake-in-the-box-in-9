import ReplayData153_0009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (andB)
open Snake9.LratFast153Replay
theorem ok288 : check start288 proof288 = true := by
  decide +kernel
#print axioms ok288
theorem ok289 : andB (check start289 proof289) (hasEmpty (replay start289 proof289) 4398) = true := by
  decide +kernel
#print axioms ok289
end Snake9.ReplayFull153
