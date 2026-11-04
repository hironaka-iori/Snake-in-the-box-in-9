import ReplayData153_0005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (andB)
open Snake9.LratFast153Replay
theorem ok188 : check start188 proof188 = true := by
  decide +kernel
#print axioms ok188
theorem ok189 : check start189 proof189 = true := by
  decide +kernel
#print axioms ok189
theorem ok190 : check start190 proof190 = true := by
  decide +kernel
#print axioms ok190
theorem ok191 : andB (check start191 proof191) (cpOk (replay start191 proof191) start192) = true := by
  decide +kernel
#print axioms ok191
end Snake9.ReplayFull153
