import Recovered129G.LocalWindowUnsat.Triple129.Data98
import Recovered129G.LocalWindowUnsat.Triple129.Data99

/-! Kernel checks of segments 389-392 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok389 : check start389 proof389 = true := by
  decide +kernel

theorem ok390 : check start390 proof390 = true := by
  decide +kernel

theorem ok391 : check start391 proof391 = true := by
  decide +kernel

theorem ok392 : andB (check start392 proof392) (cpOk (replay start392 proof392) start393) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
