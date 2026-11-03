import LocalWindowUnsat.ShareWindow144.Data210
import LocalWindowUnsat.ShareWindow144.Data211

/-! Kernel checks of segments 837-840 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok837 : check start837 proof837 = true := by
  decide +kernel

theorem ok838 : check start838 proof838 = true := by
  decide +kernel

theorem ok839 : check start839 proof839 = true := by
  decide +kernel

theorem ok840 : andB (check start840 proof840) (cpOk (replay start840 proof840) start841) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
