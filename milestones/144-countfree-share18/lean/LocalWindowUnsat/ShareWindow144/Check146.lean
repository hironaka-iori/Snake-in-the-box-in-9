import LocalWindowUnsat.ShareWindow144.Data146
import LocalWindowUnsat.ShareWindow144.Data147

/-! Kernel checks of segments 581-584 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok581 : check start581 proof581 = true := by
  decide +kernel

theorem ok582 : check start582 proof582 = true := by
  decide +kernel

theorem ok583 : check start583 proof583 = true := by
  decide +kernel

theorem ok584 : andB (check start584 proof584) (cpOk (replay start584 proof584) start585) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
