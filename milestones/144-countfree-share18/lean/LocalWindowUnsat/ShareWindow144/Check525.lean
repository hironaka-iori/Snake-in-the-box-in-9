import LocalWindowUnsat.ShareWindow144.Data525
import LocalWindowUnsat.ShareWindow144.Data526

/-! Kernel checks of segments 2097-2100 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2097 : check start2097 proof2097 = true := by
  decide +kernel

theorem ok2098 : check start2098 proof2098 = true := by
  decide +kernel

theorem ok2099 : check start2099 proof2099 = true := by
  decide +kernel

theorem ok2100 : andB (check start2100 proof2100) (cpOk (replay start2100 proof2100) start2101) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
