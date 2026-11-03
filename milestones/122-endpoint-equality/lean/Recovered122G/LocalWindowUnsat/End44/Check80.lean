import Recovered122G.LocalWindowUnsat.End44.Data80
import Recovered122G.LocalWindowUnsat.End44.Data81

/-! Kernel checks of segments 475-480 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok475 : check start475 proof475 = true := by
  decide +kernel

theorem ok476 : check start476 proof476 = true := by
  decide +kernel

theorem ok477 : check start477 proof477 = true := by
  decide +kernel

theorem ok478 : check start478 proof478 = true := by
  decide +kernel

theorem ok479 : check start479 proof479 = true := by
  decide +kernel

theorem ok480 : andB (check start480 proof480) (cpOk (replay start480 proof480) start481) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
