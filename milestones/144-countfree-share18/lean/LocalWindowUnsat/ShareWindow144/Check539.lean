import LocalWindowUnsat.ShareWindow144.Data539
import LocalWindowUnsat.ShareWindow144.Data540

/-! Kernel checks of segments 2153-2156 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2153 : check start2153 proof2153 = true := by
  decide +kernel

theorem ok2154 : check start2154 proof2154 = true := by
  decide +kernel

theorem ok2155 : check start2155 proof2155 = true := by
  decide +kernel

theorem ok2156 : andB (check start2156 proof2156) (cpOk (replay start2156 proof2156) start2157) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
