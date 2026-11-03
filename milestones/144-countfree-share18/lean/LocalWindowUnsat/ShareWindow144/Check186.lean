import LocalWindowUnsat.ShareWindow144.Data186
import LocalWindowUnsat.ShareWindow144.Data187

/-! Kernel checks of segments 741-744 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok741 : check start741 proof741 = true := by
  decide +kernel

theorem ok742 : check start742 proof742 = true := by
  decide +kernel

theorem ok743 : check start743 proof743 = true := by
  decide +kernel

theorem ok744 : andB (check start744 proof744) (cpOk (replay start744 proof744) start745) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
