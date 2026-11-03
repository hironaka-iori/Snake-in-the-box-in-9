import LocalWindowUnsat.ShareWindow144.Data29
import LocalWindowUnsat.ShareWindow144.Data30

/-! Kernel checks of segments 113-116 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok113 : check start113 proof113 = true := by
  decide +kernel

theorem ok114 : check start114 proof114 = true := by
  decide +kernel

theorem ok115 : check start115 proof115 = true := by
  decide +kernel

theorem ok116 : andB (check start116 proof116) (cpOk (replay start116 proof116) start117) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
