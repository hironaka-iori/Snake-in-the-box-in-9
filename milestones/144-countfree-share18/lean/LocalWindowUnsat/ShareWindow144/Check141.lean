import LocalWindowUnsat.ShareWindow144.Data141
import LocalWindowUnsat.ShareWindow144.Data142

/-! Kernel checks of segments 561-564 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok561 : check start561 proof561 = true := by
  decide +kernel

theorem ok562 : check start562 proof562 = true := by
  decide +kernel

theorem ok563 : check start563 proof563 = true := by
  decide +kernel

theorem ok564 : andB (check start564 proof564) (cpOk (replay start564 proof564) start565) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
