import LocalWindowUnsat.ShareWindow144.Data185
import LocalWindowUnsat.ShareWindow144.Data186

/-! Kernel checks of segments 737-740 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok737 : check start737 proof737 = true := by
  decide +kernel

theorem ok738 : check start738 proof738 = true := by
  decide +kernel

theorem ok739 : check start739 proof739 = true := by
  decide +kernel

theorem ok740 : andB (check start740 proof740) (cpOk (replay start740 proof740) start741) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
