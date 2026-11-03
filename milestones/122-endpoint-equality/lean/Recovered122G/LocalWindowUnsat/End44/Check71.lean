import Recovered122G.LocalWindowUnsat.End44.Data71
import Recovered122G.LocalWindowUnsat.End44.Data72

/-! Kernel checks of segments 421-426 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok421 : check start421 proof421 = true := by
  decide +kernel

theorem ok422 : check start422 proof422 = true := by
  decide +kernel

theorem ok423 : check start423 proof423 = true := by
  decide +kernel

theorem ok424 : check start424 proof424 = true := by
  decide +kernel

theorem ok425 : check start425 proof425 = true := by
  decide +kernel

theorem ok426 : andB (check start426 proof426) (cpOk (replay start426 proof426) start427) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
