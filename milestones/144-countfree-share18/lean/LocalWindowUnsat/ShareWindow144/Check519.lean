import LocalWindowUnsat.ShareWindow144.Data519
import LocalWindowUnsat.ShareWindow144.Data520

/-! Kernel checks of segments 2073-2076 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2073 : check start2073 proof2073 = true := by
  decide +kernel

theorem ok2074 : check start2074 proof2074 = true := by
  decide +kernel

theorem ok2075 : check start2075 proof2075 = true := by
  decide +kernel

theorem ok2076 : andB (check start2076 proof2076) (cpOk (replay start2076 proof2076) start2077) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
