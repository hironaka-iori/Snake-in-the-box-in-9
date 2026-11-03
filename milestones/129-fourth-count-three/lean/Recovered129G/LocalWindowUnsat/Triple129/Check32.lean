import Recovered129G.LocalWindowUnsat.Triple129.Data32
import Recovered129G.LocalWindowUnsat.Triple129.Data33

/-! Kernel checks of segments 125-128 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok125 : check start125 proof125 = true := by
  decide +kernel

theorem ok126 : check start126 proof126 = true := by
  decide +kernel

theorem ok127 : check start127 proof127 = true := by
  decide +kernel

theorem ok128 : andB (check start128 proof128) (cpOk (replay start128 proof128) start129) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
