import LocalWindowUnsat.ShareWindow144.Data543
import LocalWindowUnsat.ShareWindow144.Data544

/-! Kernel checks of segments 2169-2172 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2169 : check start2169 proof2169 = true := by
  decide +kernel

theorem ok2170 : check start2170 proof2170 = true := by
  decide +kernel

theorem ok2171 : check start2171 proof2171 = true := by
  decide +kernel

theorem ok2172 : andB (check start2172 proof2172) (cpOk (replay start2172 proof2172) start2173) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
