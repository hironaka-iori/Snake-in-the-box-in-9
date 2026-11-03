import Recovered122G.LocalWindowUnsat.End44.Data93
import Recovered122G.LocalWindowUnsat.End44.Data94

/-! Kernel checks of segments 553-558 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok553 : check start553 proof553 = true := by
  decide +kernel

theorem ok554 : check start554 proof554 = true := by
  decide +kernel

theorem ok555 : check start555 proof555 = true := by
  decide +kernel

theorem ok556 : check start556 proof556 = true := by
  decide +kernel

theorem ok557 : check start557 proof557 = true := by
  decide +kernel

theorem ok558 : andB (check start558 proof558) (cpOk (replay start558 proof558) start559) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
