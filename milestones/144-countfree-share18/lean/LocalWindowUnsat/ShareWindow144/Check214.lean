import LocalWindowUnsat.ShareWindow144.Data214
import LocalWindowUnsat.ShareWindow144.Data215

/-! Kernel checks of segments 853-856 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok853 : check start853 proof853 = true := by
  decide +kernel

theorem ok854 : check start854 proof854 = true := by
  decide +kernel

theorem ok855 : check start855 proof855 = true := by
  decide +kernel

theorem ok856 : andB (check start856 proof856) (cpOk (replay start856 proof856) start857) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
