import LocalWindowUnsat.ShareWindow144.Data27
import LocalWindowUnsat.ShareWindow144.Data28

/-! Kernel checks of segments 105-108 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok105 : check start105 proof105 = true := by
  decide +kernel

theorem ok106 : check start106 proof106 = true := by
  decide +kernel

theorem ok107 : check start107 proof107 = true := by
  decide +kernel

theorem ok108 : andB (check start108 proof108) (cpOk (replay start108 proof108) start109) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
