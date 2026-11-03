import Recovered129G.LocalWindowUnsat.Triple129.Data78
import Recovered129G.LocalWindowUnsat.Triple129.Data79

/-! Kernel checks of segments 309-312 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok309 : check start309 proof309 = true := by
  decide +kernel

theorem ok310 : check start310 proof310 = true := by
  decide +kernel

theorem ok311 : check start311 proof311 = true := by
  decide +kernel

theorem ok312 : andB (check start312 proof312) (cpOk (replay start312 proof312) start313) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
