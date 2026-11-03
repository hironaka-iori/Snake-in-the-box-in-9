import LocalWindowUnsat.ShareWindow144.Data189
import LocalWindowUnsat.ShareWindow144.Data190

/-! Kernel checks of segments 753-756 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok753 : check start753 proof753 = true := by
  decide +kernel

theorem ok754 : check start754 proof754 = true := by
  decide +kernel

theorem ok755 : check start755 proof755 = true := by
  decide +kernel

theorem ok756 : andB (check start756 proof756) (cpOk (replay start756 proof756) start757) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
