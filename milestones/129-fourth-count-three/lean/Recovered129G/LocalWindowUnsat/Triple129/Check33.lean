import Recovered129G.LocalWindowUnsat.Triple129.Data33
import Recovered129G.LocalWindowUnsat.Triple129.Data34

/-! Kernel checks of segments 129-132 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok129 : check start129 proof129 = true := by
  decide +kernel

theorem ok130 : check start130 proof130 = true := by
  decide +kernel

theorem ok131 : check start131 proof131 = true := by
  decide +kernel

theorem ok132 : andB (check start132 proof132) (cpOk (replay start132 proof132) start133) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
