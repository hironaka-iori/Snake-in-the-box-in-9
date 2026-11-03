import LocalWindowUnsat.ShareWindow144.Data180
import LocalWindowUnsat.ShareWindow144.Data181

/-! Kernel checks of segments 717-720 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok717 : check start717 proof717 = true := by
  decide +kernel

theorem ok718 : check start718 proof718 = true := by
  decide +kernel

theorem ok719 : check start719 proof719 = true := by
  decide +kernel

theorem ok720 : andB (check start720 proof720) (cpOk (replay start720 proof720) start721) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
