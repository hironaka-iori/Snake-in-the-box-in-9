import LocalWindowUnsat.ShareWindow144.Data510
import LocalWindowUnsat.ShareWindow144.Data511

/-! Kernel checks of segments 2037-2040 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2037 : check start2037 proof2037 = true := by
  decide +kernel

theorem ok2038 : check start2038 proof2038 = true := by
  decide +kernel

theorem ok2039 : check start2039 proof2039 = true := by
  decide +kernel

theorem ok2040 : andB (check start2040 proof2040) (cpOk (replay start2040 proof2040) start2041) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
