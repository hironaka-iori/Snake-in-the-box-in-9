import LocalWindowUnsat.ShareWindow144.Data105
import LocalWindowUnsat.ShareWindow144.Data106

/-! Kernel checks of segments 417-420 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok417 : check start417 proof417 = true := by
  decide +kernel

theorem ok418 : check start418 proof418 = true := by
  decide +kernel

theorem ok419 : check start419 proof419 = true := by
  decide +kernel

theorem ok420 : andB (check start420 proof420) (cpOk (replay start420 proof420) start421) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
