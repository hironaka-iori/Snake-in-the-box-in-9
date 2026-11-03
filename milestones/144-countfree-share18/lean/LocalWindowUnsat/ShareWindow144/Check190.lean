import LocalWindowUnsat.ShareWindow144.Data190
import LocalWindowUnsat.ShareWindow144.Data191

/-! Kernel checks of segments 757-760 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok757 : check start757 proof757 = true := by
  decide +kernel

theorem ok758 : check start758 proof758 = true := by
  decide +kernel

theorem ok759 : check start759 proof759 = true := by
  decide +kernel

theorem ok760 : andB (check start760 proof760) (cpOk (replay start760 proof760) start761) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
