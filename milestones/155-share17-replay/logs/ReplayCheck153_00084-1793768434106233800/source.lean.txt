import ReplayData153_0002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (andB)
open Snake9.LratFast153Replay
theorem ok84 : check start84 proof84 = true := by
  decide +kernel
#print axioms ok84
theorem ok85 : check start85 proof85 = true := by
  decide +kernel
#print axioms ok85
theorem ok86 : check start86 proof86 = true := by
  decide +kernel
#print axioms ok86
theorem ok87 : check start87 proof87 = true := by
  decide +kernel
#print axioms ok87
end Snake9.ReplayFull153
