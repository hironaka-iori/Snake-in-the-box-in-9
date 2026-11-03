import Recovered129G.LocalWindowUnsat.Triple129.Data83
import Recovered129G.LocalWindowUnsat.Triple129.Data84

/-! Kernel checks of segments 329-332 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok329 : check start329 proof329 = true := by
  decide +kernel

theorem ok330 : check start330 proof330 = true := by
  decide +kernel

theorem ok331 : check start331 proof331 = true := by
  decide +kernel

theorem ok332 : andB (check start332 proof332) (cpOk (replay start332 proof332) start333) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
