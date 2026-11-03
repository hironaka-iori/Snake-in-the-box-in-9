import LocalWindowUnsat.ShareWindow144.Data125
import LocalWindowUnsat.ShareWindow144.Data126

/-! Kernel checks of segments 497-500 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok497 : check start497 proof497 = true := by
  decide +kernel

theorem ok498 : check start498 proof498 = true := by
  decide +kernel

theorem ok499 : check start499 proof499 = true := by
  decide +kernel

theorem ok500 : andB (check start500 proof500) (cpOk (replay start500 proof500) start501) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
