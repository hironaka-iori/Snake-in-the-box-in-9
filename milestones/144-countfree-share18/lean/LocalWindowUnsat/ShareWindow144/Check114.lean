import LocalWindowUnsat.ShareWindow144.Data114
import LocalWindowUnsat.ShareWindow144.Data115

/-! Kernel checks of segments 453-456 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok453 : check start453 proof453 = true := by
  decide +kernel

theorem ok454 : check start454 proof454 = true := by
  decide +kernel

theorem ok455 : check start455 proof455 = true := by
  decide +kernel

theorem ok456 : andB (check start456 proof456) (cpOk (replay start456 proof456) start457) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
