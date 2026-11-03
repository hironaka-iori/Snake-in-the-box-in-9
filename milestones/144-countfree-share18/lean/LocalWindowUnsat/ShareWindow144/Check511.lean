import LocalWindowUnsat.ShareWindow144.Data511
import LocalWindowUnsat.ShareWindow144.Data512

/-! Kernel checks of segments 2041-2044 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2041 : check start2041 proof2041 = true := by
  decide +kernel

theorem ok2042 : check start2042 proof2042 = true := by
  decide +kernel

theorem ok2043 : check start2043 proof2043 = true := by
  decide +kernel

theorem ok2044 : andB (check start2044 proof2044) (cpOk (replay start2044 proof2044) start2045) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
