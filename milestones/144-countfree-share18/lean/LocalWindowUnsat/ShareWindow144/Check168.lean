import LocalWindowUnsat.ShareWindow144.Data168
import LocalWindowUnsat.ShareWindow144.Data169

/-! Kernel checks of segments 669-672 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok669 : check start669 proof669 = true := by
  decide +kernel

theorem ok670 : check start670 proof670 = true := by
  decide +kernel

theorem ok671 : check start671 proof671 = true := by
  decide +kernel

theorem ok672 : andB (check start672 proof672) (cpOk (replay start672 proof672) start673) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
