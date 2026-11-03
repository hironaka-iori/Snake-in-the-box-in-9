import LocalWindowUnsat.ShareWindow144.Data165
import LocalWindowUnsat.ShareWindow144.Data166

/-! Kernel checks of segments 657-660 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok657 : check start657 proof657 = true := by
  decide +kernel

theorem ok658 : check start658 proof658 = true := by
  decide +kernel

theorem ok659 : check start659 proof659 = true := by
  decide +kernel

theorem ok660 : andB (check start660 proof660) (cpOk (replay start660 proof660) start661) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
