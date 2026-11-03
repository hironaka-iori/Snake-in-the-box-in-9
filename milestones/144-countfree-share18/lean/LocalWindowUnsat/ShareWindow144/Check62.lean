import LocalWindowUnsat.ShareWindow144.Data62
import LocalWindowUnsat.ShareWindow144.Data63

/-! Kernel checks of segments 245-248 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok245 : check start245 proof245 = true := by
  decide +kernel

theorem ok246 : check start246 proof246 = true := by
  decide +kernel

theorem ok247 : check start247 proof247 = true := by
  decide +kernel

theorem ok248 : andB (check start248 proof248) (cpOk (replay start248 proof248) start249) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
