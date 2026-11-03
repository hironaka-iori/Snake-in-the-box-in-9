import LocalWindowUnsat.ShareWindow144.Data83
import LocalWindowUnsat.ShareWindow144.Data84

/-! Kernel checks of segments 329-332 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok329 : check start329 proof329 = true := by
  decide +kernel

theorem ok330 : check start330 proof330 = true := by
  decide +kernel

theorem ok331 : check start331 proof331 = true := by
  decide +kernel

theorem ok332 : andB (check start332 proof332) (cpOk (replay start332 proof332) start333) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
