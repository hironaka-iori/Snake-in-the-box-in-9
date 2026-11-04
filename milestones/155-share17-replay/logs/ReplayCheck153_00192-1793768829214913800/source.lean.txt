import ReplayData153_0006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (andB)
open Snake9.LratFast153Replay
theorem ok192 : check start192 proof192 = true := by
  decide +kernel
#print axioms ok192
theorem ok193 : check start193 proof193 = true := by
  decide +kernel
#print axioms ok193
theorem ok194 : check start194 proof194 = true := by
  decide +kernel
#print axioms ok194
theorem ok195 : check start195 proof195 = true := by
  decide +kernel
#print axioms ok195
end Snake9.ReplayFull153
