import LocalWindowUnsat.ShareWindow144.Data94
import LocalWindowUnsat.ShareWindow144.Data95

/-! Kernel checks of segments 373-376 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok373 : check start373 proof373 = true := by
  decide +kernel

theorem ok374 : check start374 proof374 = true := by
  decide +kernel

theorem ok375 : check start375 proof375 = true := by
  decide +kernel

theorem ok376 : andB (check start376 proof376) (cpOk (replay start376 proof376) start377) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
