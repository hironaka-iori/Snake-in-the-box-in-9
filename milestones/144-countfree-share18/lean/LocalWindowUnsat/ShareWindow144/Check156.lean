import LocalWindowUnsat.ShareWindow144.Data156
import LocalWindowUnsat.ShareWindow144.Data157

/-! Kernel checks of segments 621-624 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok621 : check start621 proof621 = true := by
  decide +kernel

theorem ok622 : check start622 proof622 = true := by
  decide +kernel

theorem ok623 : check start623 proof623 = true := by
  decide +kernel

theorem ok624 : andB (check start624 proof624) (cpOk (replay start624 proof624) start625) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
