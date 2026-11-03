import LocalWindowUnsat.ShareWindow144.Data241
import LocalWindowUnsat.ShareWindow144.Data242

/-! Kernel checks of segments 961-964 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok961 : check start961 proof961 = true := by
  decide +kernel

theorem ok962 : check start962 proof962 = true := by
  decide +kernel

theorem ok963 : check start963 proof963 = true := by
  decide +kernel

theorem ok964 : andB (check start964 proof964) (cpOk (replay start964 proof964) start965) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
