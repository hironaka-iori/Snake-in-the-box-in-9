import LocalWindowUnsat.ShareWindow144.Data164
import LocalWindowUnsat.ShareWindow144.Data165

/-! Kernel checks of segments 653-656 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok653 : check start653 proof653 = true := by
  decide +kernel

theorem ok654 : check start654 proof654 = true := by
  decide +kernel

theorem ok655 : check start655 proof655 = true := by
  decide +kernel

theorem ok656 : andB (check start656 proof656) (cpOk (replay start656 proof656) start657) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
