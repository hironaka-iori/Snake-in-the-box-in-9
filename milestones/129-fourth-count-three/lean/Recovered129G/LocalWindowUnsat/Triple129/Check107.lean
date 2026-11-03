import Recovered129G.LocalWindowUnsat.Triple129.Data107
import Recovered129G.LocalWindowUnsat.Triple129.Data108

/-! Kernel checks of segments 425-428 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok425 : check start425 proof425 = true := by
  decide +kernel

theorem ok426 : check start426 proof426 = true := by
  decide +kernel

theorem ok427 : check start427 proof427 = true := by
  decide +kernel

theorem ok428 : andB (check start428 proof428) (cpOk (replay start428 proof428) start429) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
