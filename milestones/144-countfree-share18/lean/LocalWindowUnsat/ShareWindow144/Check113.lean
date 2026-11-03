import LocalWindowUnsat.ShareWindow144.Data113
import LocalWindowUnsat.ShareWindow144.Data114

/-! Kernel checks of segments 449-452 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok449 : check start449 proof449 = true := by
  decide +kernel

theorem ok450 : check start450 proof450 = true := by
  decide +kernel

theorem ok451 : check start451 proof451 = true := by
  decide +kernel

theorem ok452 : andB (check start452 proof452) (cpOk (replay start452 proof452) start453) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
