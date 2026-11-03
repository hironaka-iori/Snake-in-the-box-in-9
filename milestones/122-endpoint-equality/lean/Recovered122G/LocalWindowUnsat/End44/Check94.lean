import Recovered122G.LocalWindowUnsat.End44.Data94
import Recovered122G.LocalWindowUnsat.End44.Data95

/-! Kernel checks of segments 559-564 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok559 : check start559 proof559 = true := by
  decide +kernel

theorem ok560 : check start560 proof560 = true := by
  decide +kernel

theorem ok561 : check start561 proof561 = true := by
  decide +kernel

theorem ok562 : check start562 proof562 = true := by
  decide +kernel

theorem ok563 : check start563 proof563 = true := by
  decide +kernel

theorem ok564 : andB (check start564 proof564) (cpOk (replay start564 proof564) start565) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
