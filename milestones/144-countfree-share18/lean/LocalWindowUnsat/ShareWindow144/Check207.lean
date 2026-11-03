import LocalWindowUnsat.ShareWindow144.Data207
import LocalWindowUnsat.ShareWindow144.Data208

/-! Kernel checks of segments 825-828 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok825 : check start825 proof825 = true := by
  decide +kernel

theorem ok826 : check start826 proof826 = true := by
  decide +kernel

theorem ok827 : check start827 proof827 = true := by
  decide +kernel

theorem ok828 : andB (check start828 proof828) (cpOk (replay start828 proof828) start829) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
