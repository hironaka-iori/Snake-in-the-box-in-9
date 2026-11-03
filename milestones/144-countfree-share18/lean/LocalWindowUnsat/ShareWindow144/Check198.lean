import LocalWindowUnsat.ShareWindow144.Data198
import LocalWindowUnsat.ShareWindow144.Data199

/-! Kernel checks of segments 789-792 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok789 : check start789 proof789 = true := by
  decide +kernel

theorem ok790 : check start790 proof790 = true := by
  decide +kernel

theorem ok791 : check start791 proof791 = true := by
  decide +kernel

theorem ok792 : andB (check start792 proof792) (cpOk (replay start792 proof792) start793) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
