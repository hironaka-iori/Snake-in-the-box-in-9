import Recovered122G.LocalWindowUnsat.End35.Data79
import Recovered122G.LocalWindowUnsat.End35.Data80

/-! Kernel checks of segments 469-474 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok469 : check start469 proof469 = true := by
  decide +kernel

theorem ok470 : check start470 proof470 = true := by
  decide +kernel

theorem ok471 : check start471 proof471 = true := by
  decide +kernel

theorem ok472 : check start472 proof472 = true := by
  decide +kernel

theorem ok473 : check start473 proof473 = true := by
  decide +kernel

theorem ok474 : andB (check start474 proof474) (cpOk (replay start474 proof474) start475) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
