import Recovered129G.LocalWindowUnsat.Triple129.Data19
import Recovered129G.LocalWindowUnsat.Triple129.Data20

/-! Kernel checks of segments 73-76 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok73 : check start73 proof73 = true := by
  decide +kernel

theorem ok74 : check start74 proof74 = true := by
  decide +kernel

theorem ok75 : check start75 proof75 = true := by
  decide +kernel

theorem ok76 : andB (check start76 proof76) (cpOk (replay start76 proof76) start77) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
