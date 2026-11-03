import LocalWindowUnsat.ShareWindow144.Data204
import LocalWindowUnsat.ShareWindow144.Data205

/-! Kernel checks of segments 813-816 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok813 : check start813 proof813 = true := by
  decide +kernel

theorem ok814 : check start814 proof814 = true := by
  decide +kernel

theorem ok815 : check start815 proof815 = true := by
  decide +kernel

theorem ok816 : andB (check start816 proof816) (cpOk (replay start816 proof816) start817) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
