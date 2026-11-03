import Recovered129G.LocalWindowUnsat.Triple129.Data20
import Recovered129G.LocalWindowUnsat.Triple129.Data21

/-! Kernel checks of segments 77-80 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok77 : check start77 proof77 = true := by
  decide +kernel

theorem ok78 : check start78 proof78 = true := by
  decide +kernel

theorem ok79 : check start79 proof79 = true := by
  decide +kernel

theorem ok80 : andB (check start80 proof80) (cpOk (replay start80 proof80) start81) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
