import LocalWindowUnsat.ShareWindow144.Data159
import LocalWindowUnsat.ShareWindow144.Data160

/-! Kernel checks of segments 633-636 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok633 : check start633 proof633 = true := by
  decide +kernel

theorem ok634 : check start634 proof634 = true := by
  decide +kernel

theorem ok635 : check start635 proof635 = true := by
  decide +kernel

theorem ok636 : andB (check start636 proof636) (cpOk (replay start636 proof636) start637) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
