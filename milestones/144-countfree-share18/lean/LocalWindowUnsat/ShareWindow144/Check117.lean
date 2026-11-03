import LocalWindowUnsat.ShareWindow144.Data117
import LocalWindowUnsat.ShareWindow144.Data118

/-! Kernel checks of segments 465-468 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok465 : check start465 proof465 = true := by
  decide +kernel

theorem ok466 : check start466 proof466 = true := by
  decide +kernel

theorem ok467 : check start467 proof467 = true := by
  decide +kernel

theorem ok468 : andB (check start468 proof468) (cpOk (replay start468 proof468) start469) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
