import Recovered122G.LocalWindowUnsat.End44.Data98
import Recovered122G.LocalWindowUnsat.End44.Data99

/-! Kernel checks of segments 583-588 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok583 : check start583 proof583 = true := by
  decide +kernel

theorem ok584 : check start584 proof584 = true := by
  decide +kernel

theorem ok585 : check start585 proof585 = true := by
  decide +kernel

theorem ok586 : check start586 proof586 = true := by
  decide +kernel

theorem ok587 : check start587 proof587 = true := by
  decide +kernel

theorem ok588 : andB (check start588 proof588) (cpOk (replay start588 proof588) start589) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
