import Recovered129G.LocalWindowUnsat.Triple129.Data18
import Recovered129G.LocalWindowUnsat.Triple129.Data19

/-! Kernel checks of segments 69-72 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok69 : check start69 proof69 = true := by
  decide +kernel

theorem ok70 : check start70 proof70 = true := by
  decide +kernel

theorem ok71 : check start71 proof71 = true := by
  decide +kernel

theorem ok72 : andB (check start72 proof72) (cpOk (replay start72 proof72) start73) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
