import Recovered122G.LocalWindowUnsat.End44.Data97
import Recovered122G.LocalWindowUnsat.End44.Data98

/-! Kernel checks of segments 577-582 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok577 : check start577 proof577 = true := by
  decide +kernel

theorem ok578 : check start578 proof578 = true := by
  decide +kernel

theorem ok579 : check start579 proof579 = true := by
  decide +kernel

theorem ok580 : check start580 proof580 = true := by
  decide +kernel

theorem ok581 : check start581 proof581 = true := by
  decide +kernel

theorem ok582 : andB (check start582 proof582) (cpOk (replay start582 proof582) start583) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
