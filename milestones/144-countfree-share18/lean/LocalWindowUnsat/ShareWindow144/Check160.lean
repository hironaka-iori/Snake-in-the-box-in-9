import LocalWindowUnsat.ShareWindow144.Data160
import LocalWindowUnsat.ShareWindow144.Data161

/-! Kernel checks of segments 637-640 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok637 : check start637 proof637 = true := by
  decide +kernel

theorem ok638 : check start638 proof638 = true := by
  decide +kernel

theorem ok639 : check start639 proof639 = true := by
  decide +kernel

theorem ok640 : andB (check start640 proof640) (cpOk (replay start640 proof640) start641) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
