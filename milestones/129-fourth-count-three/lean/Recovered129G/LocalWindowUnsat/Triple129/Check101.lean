import Recovered129G.LocalWindowUnsat.Triple129.Data101
import Recovered129G.LocalWindowUnsat.Triple129.Data102

/-! Kernel checks of segments 401-404 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok401 : check start401 proof401 = true := by
  decide +kernel

theorem ok402 : check start402 proof402 = true := by
  decide +kernel

theorem ok403 : check start403 proof403 = true := by
  decide +kernel

theorem ok404 : andB (check start404 proof404) (cpOk (replay start404 proof404) start405) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
