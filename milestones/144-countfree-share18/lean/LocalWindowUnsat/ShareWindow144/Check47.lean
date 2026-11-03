import LocalWindowUnsat.ShareWindow144.Data47
import LocalWindowUnsat.ShareWindow144.Data48

/-! Kernel checks of segments 185-188 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok185 : check start185 proof185 = true := by
  decide +kernel

theorem ok186 : check start186 proof186 = true := by
  decide +kernel

theorem ok187 : check start187 proof187 = true := by
  decide +kernel

theorem ok188 : andB (check start188 proof188) (cpOk (replay start188 proof188) start189) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
