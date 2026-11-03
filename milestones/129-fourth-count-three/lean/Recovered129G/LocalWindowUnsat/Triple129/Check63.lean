import Recovered129G.LocalWindowUnsat.Triple129.Data63
import Recovered129G.LocalWindowUnsat.Triple129.Data64

/-! Kernel checks of segments 249-252 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok249 : check start249 proof249 = true := by
  decide +kernel

theorem ok250 : check start250 proof250 = true := by
  decide +kernel

theorem ok251 : check start251 proof251 = true := by
  decide +kernel

theorem ok252 : andB (check start252 proof252) (cpOk (replay start252 proof252) start253) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
