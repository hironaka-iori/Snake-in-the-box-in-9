import Recovered129G.LocalWindowUnsat.Triple129.Data61
import Recovered129G.LocalWindowUnsat.Triple129.Data62

/-! Kernel checks of segments 241-244 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok241 : check start241 proof241 = true := by
  decide +kernel

theorem ok242 : check start242 proof242 = true := by
  decide +kernel

theorem ok243 : check start243 proof243 = true := by
  decide +kernel

theorem ok244 : andB (check start244 proof244) (cpOk (replay start244 proof244) start245) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
