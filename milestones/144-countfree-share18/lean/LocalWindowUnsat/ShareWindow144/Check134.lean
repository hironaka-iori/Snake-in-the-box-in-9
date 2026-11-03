import LocalWindowUnsat.ShareWindow144.Data134
import LocalWindowUnsat.ShareWindow144.Data135

/-! Kernel checks of segments 533-536 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok533 : check start533 proof533 = true := by
  decide +kernel

theorem ok534 : check start534 proof534 = true := by
  decide +kernel

theorem ok535 : check start535 proof535 = true := by
  decide +kernel

theorem ok536 : andB (check start536 proof536) (cpOk (replay start536 proof536) start537) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
