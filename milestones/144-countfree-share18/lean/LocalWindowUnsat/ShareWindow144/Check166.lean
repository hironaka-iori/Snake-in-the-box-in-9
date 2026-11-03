import LocalWindowUnsat.ShareWindow144.Data166
import LocalWindowUnsat.ShareWindow144.Data167

/-! Kernel checks of segments 661-664 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok661 : check start661 proof661 = true := by
  decide +kernel

theorem ok662 : check start662 proof662 = true := by
  decide +kernel

theorem ok663 : check start663 proof663 = true := by
  decide +kernel

theorem ok664 : andB (check start664 proof664) (cpOk (replay start664 proof664) start665) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
