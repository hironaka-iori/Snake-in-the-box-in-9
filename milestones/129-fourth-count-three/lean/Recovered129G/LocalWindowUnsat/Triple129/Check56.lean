import Recovered129G.LocalWindowUnsat.Triple129.Data56
import Recovered129G.LocalWindowUnsat.Triple129.Data57

/-! Kernel checks of segments 221-224 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok221 : check start221 proof221 = true := by
  decide +kernel

theorem ok222 : check start222 proof222 = true := by
  decide +kernel

theorem ok223 : check start223 proof223 = true := by
  decide +kernel

theorem ok224 : andB (check start224 proof224) (cpOk (replay start224 proof224) start225) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
