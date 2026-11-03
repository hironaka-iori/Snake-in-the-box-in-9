import LocalWindowUnsat.ShareWindow144.Data108
import LocalWindowUnsat.ShareWindow144.Data109

/-! Kernel checks of segments 429-432 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok429 : check start429 proof429 = true := by
  decide +kernel

theorem ok430 : check start430 proof430 = true := by
  decide +kernel

theorem ok431 : check start431 proof431 = true := by
  decide +kernel

theorem ok432 : andB (check start432 proof432) (cpOk (replay start432 proof432) start433) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
