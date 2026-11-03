import Recovered122G.LocalWindowUnsat.End44.Data1
import Recovered122G.LocalWindowUnsat.End44.Data2

/-! Kernel checks of segments 1-6 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok1 : check start1 proof1 = true := by
  decide +kernel

theorem ok2 : check start2 proof2 = true := by
  decide +kernel

theorem ok3 : check start3 proof3 = true := by
  decide +kernel

theorem ok4 : check start4 proof4 = true := by
  decide +kernel

theorem ok5 : check start5 proof5 = true := by
  decide +kernel

theorem ok6 : andB (check start6 proof6) (cpOk (replay start6 proof6) start7) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
