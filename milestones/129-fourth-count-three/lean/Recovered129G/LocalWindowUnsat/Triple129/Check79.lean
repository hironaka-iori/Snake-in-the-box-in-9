import Recovered129G.LocalWindowUnsat.Triple129.Data79
import Recovered129G.LocalWindowUnsat.Triple129.Data80

/-! Kernel checks of segments 313-316 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok313 : check start313 proof313 = true := by
  decide +kernel

theorem ok314 : check start314 proof314 = true := by
  decide +kernel

theorem ok315 : check start315 proof315 = true := by
  decide +kernel

theorem ok316 : andB (check start316 proof316) (cpOk (replay start316 proof316) start317) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
