import ReplayPilotData153
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayPilot153
open Snake9.Lrat153Replay (andB)
open Snake9.LratFast153Replay
theorem prefix_check : andB (check Snake9.ReplayData153.start proof)
    (cpOk (replay Snake9.ReplayData153.start proof) afterPrefix) = true := by
  decide +kernel
#print axioms prefix_check
end Snake9.ReplayPilot153
