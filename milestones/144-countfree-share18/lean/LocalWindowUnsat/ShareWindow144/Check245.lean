import LocalWindowUnsat.ShareWindow144.Data245
import LocalWindowUnsat.ShareWindow144.Data246

/-! Kernel checks of segments 977-980 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok977 : check start977 proof977 = true := by
  decide +kernel

theorem ok978 : check start978 proof978 = true := by
  decide +kernel

theorem ok979 : check start979 proof979 = true := by
  decide +kernel

theorem ok980 : andB (check start980 proof980) (cpOk (replay start980 proof980) start981) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
