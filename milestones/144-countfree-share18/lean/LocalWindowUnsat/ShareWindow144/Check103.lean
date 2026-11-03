import LocalWindowUnsat.ShareWindow144.Data103
import LocalWindowUnsat.ShareWindow144.Data104

/-! Kernel checks of segments 409-412 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok409 : check start409 proof409 = true := by
  decide +kernel

theorem ok410 : check start410 proof410 = true := by
  decide +kernel

theorem ok411 : check start411 proof411 = true := by
  decide +kernel

theorem ok412 : andB (check start412 proof412) (cpOk (replay start412 proof412) start413) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
