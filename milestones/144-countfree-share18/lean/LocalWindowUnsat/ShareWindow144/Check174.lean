import LocalWindowUnsat.ShareWindow144.Data174
import LocalWindowUnsat.ShareWindow144.Data175

/-! Kernel checks of segments 693-696 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok693 : check start693 proof693 = true := by
  decide +kernel

theorem ok694 : check start694 proof694 = true := by
  decide +kernel

theorem ok695 : check start695 proof695 = true := by
  decide +kernel

theorem ok696 : andB (check start696 proof696) (cpOk (replay start696 proof696) start697) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
