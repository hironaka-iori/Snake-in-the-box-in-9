import ReplayData153_0005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (andB)
open Snake9.LratFast153Replay
theorem ok160 : check start160 proof160 = true := by
  decide +kernel
#print axioms ok160
theorem ok161 : check start161 proof161 = true := by
  decide +kernel
#print axioms ok161
theorem ok162 : check start162 proof162 = true := by
  decide +kernel
#print axioms ok162
theorem ok163 : check start163 proof163 = true := by
  decide +kernel
#print axioms ok163
end Snake9.ReplayFull153
