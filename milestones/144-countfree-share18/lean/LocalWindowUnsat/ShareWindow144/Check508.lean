import LocalWindowUnsat.ShareWindow144.Data508
import LocalWindowUnsat.ShareWindow144.Data509

/-! Kernel checks of segments 2029-2032 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2029 : check start2029 proof2029 = true := by
  decide +kernel

theorem ok2030 : check start2030 proof2030 = true := by
  decide +kernel

theorem ok2031 : check start2031 proof2031 = true := by
  decide +kernel

theorem ok2032 : andB (check start2032 proof2032) (cpOk (replay start2032 proof2032) start2033) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
