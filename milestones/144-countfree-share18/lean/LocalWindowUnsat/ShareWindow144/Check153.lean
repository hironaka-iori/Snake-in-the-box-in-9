import LocalWindowUnsat.ShareWindow144.Data153
import LocalWindowUnsat.ShareWindow144.Data154

/-! Kernel checks of segments 609-612 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok609 : check start609 proof609 = true := by
  decide +kernel

theorem ok610 : check start610 proof610 = true := by
  decide +kernel

theorem ok611 : check start611 proof611 = true := by
  decide +kernel

theorem ok612 : andB (check start612 proof612) (cpOk (replay start612 proof612) start613) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
