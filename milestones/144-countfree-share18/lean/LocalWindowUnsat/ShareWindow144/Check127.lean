import LocalWindowUnsat.ShareWindow144.Data127
import LocalWindowUnsat.ShareWindow144.Data128

/-! Kernel checks of segments 505-508 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok505 : check start505 proof505 = true := by
  decide +kernel

theorem ok506 : check start506 proof506 = true := by
  decide +kernel

theorem ok507 : check start507 proof507 = true := by
  decide +kernel

theorem ok508 : andB (check start508 proof508) (cpOk (replay start508 proof508) start509) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
