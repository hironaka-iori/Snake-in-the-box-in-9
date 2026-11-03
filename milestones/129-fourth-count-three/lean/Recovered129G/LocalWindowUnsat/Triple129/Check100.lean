import Recovered129G.LocalWindowUnsat.Triple129.Data100
import Recovered129G.LocalWindowUnsat.Triple129.Data101

/-! Kernel checks of segments 397-400 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok397 : check start397 proof397 = true := by
  decide +kernel

theorem ok398 : check start398 proof398 = true := by
  decide +kernel

theorem ok399 : check start399 proof399 = true := by
  decide +kernel

theorem ok400 : andB (check start400 proof400) (cpOk (replay start400 proof400) start401) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
