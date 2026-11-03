import LocalWindowUnsat.ShareWindow144.Data200
import LocalWindowUnsat.ShareWindow144.Data201

/-! Kernel checks of segments 797-800 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok797 : check start797 proof797 = true := by
  decide +kernel

theorem ok798 : check start798 proof798 = true := by
  decide +kernel

theorem ok799 : check start799 proof799 = true := by
  decide +kernel

theorem ok800 : andB (check start800 proof800) (cpOk (replay start800 proof800) start801) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
