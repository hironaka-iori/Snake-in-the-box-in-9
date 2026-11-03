import LocalWindowUnsat.ShareWindow144.Data184
import LocalWindowUnsat.ShareWindow144.Data185

/-! Kernel checks of segments 733-736 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok733 : check start733 proof733 = true := by
  decide +kernel

theorem ok734 : check start734 proof734 = true := by
  decide +kernel

theorem ok735 : check start735 proof735 = true := by
  decide +kernel

theorem ok736 : andB (check start736 proof736) (cpOk (replay start736 proof736) start737) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
