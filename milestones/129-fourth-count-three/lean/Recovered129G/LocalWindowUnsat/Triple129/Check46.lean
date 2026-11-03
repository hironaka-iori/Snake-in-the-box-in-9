import Recovered129G.LocalWindowUnsat.Triple129.Data46
import Recovered129G.LocalWindowUnsat.Triple129.Data47

/-! Kernel checks of segments 181-184 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok181 : check start181 proof181 = true := by
  decide +kernel

theorem ok182 : check start182 proof182 = true := by
  decide +kernel

theorem ok183 : check start183 proof183 = true := by
  decide +kernel

theorem ok184 : andB (check start184 proof184) (cpOk (replay start184 proof184) start185) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
