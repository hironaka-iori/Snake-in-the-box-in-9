import LocalWindowUnsat.ShareWindow144.Data133
import LocalWindowUnsat.ShareWindow144.Data134

/-! Kernel checks of segments 529-532 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok529 : check start529 proof529 = true := by
  decide +kernel

theorem ok530 : check start530 proof530 = true := by
  decide +kernel

theorem ok531 : check start531 proof531 = true := by
  decide +kernel

theorem ok532 : andB (check start532 proof532) (cpOk (replay start532 proof532) start533) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
