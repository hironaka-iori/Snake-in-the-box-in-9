import ReplayData153_0004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (andB)
open Snake9.LratFast153Replay
theorem ok156 : check start156 proof156 = true := by
  decide +kernel
#print axioms ok156
theorem ok157 : check start157 proof157 = true := by
  decide +kernel
#print axioms ok157
theorem ok158 : check start158 proof158 = true := by
  decide +kernel
#print axioms ok158
theorem ok159 : andB (check start159 proof159) (cpOk (replay start159 proof159) start160) = true := by
  decide +kernel
#print axioms ok159
end Snake9.ReplayFull153
