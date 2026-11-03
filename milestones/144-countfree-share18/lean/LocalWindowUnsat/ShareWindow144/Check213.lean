import LocalWindowUnsat.ShareWindow144.Data213
import LocalWindowUnsat.ShareWindow144.Data214

/-! Kernel checks of segments 849-852 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok849 : check start849 proof849 = true := by
  decide +kernel

theorem ok850 : check start850 proof850 = true := by
  decide +kernel

theorem ok851 : check start851 proof851 = true := by
  decide +kernel

theorem ok852 : andB (check start852 proof852) (cpOk (replay start852 proof852) start853) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
