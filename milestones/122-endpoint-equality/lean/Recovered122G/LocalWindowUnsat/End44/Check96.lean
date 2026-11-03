import Recovered122G.LocalWindowUnsat.End44.Data96
import Recovered122G.LocalWindowUnsat.End44.Data97

/-! Kernel checks of segments 571-576 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok571 : check start571 proof571 = true := by
  decide +kernel

theorem ok572 : check start572 proof572 = true := by
  decide +kernel

theorem ok573 : check start573 proof573 = true := by
  decide +kernel

theorem ok574 : check start574 proof574 = true := by
  decide +kernel

theorem ok575 : check start575 proof575 = true := by
  decide +kernel

theorem ok576 : andB (check start576 proof576) (cpOk (replay start576 proof576) start577) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
