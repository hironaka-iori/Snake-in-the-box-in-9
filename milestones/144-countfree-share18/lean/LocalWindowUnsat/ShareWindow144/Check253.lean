import LocalWindowUnsat.ShareWindow144.Data253
import LocalWindowUnsat.ShareWindow144.Data254

/-! Kernel checks of segments 1009-1012 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1009 : check start1009 proof1009 = true := by
  decide +kernel

theorem ok1010 : check start1010 proof1010 = true := by
  decide +kernel

theorem ok1011 : check start1011 proof1011 = true := by
  decide +kernel

theorem ok1012 : andB (check start1012 proof1012) (cpOk (replay start1012 proof1012) start1013) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
