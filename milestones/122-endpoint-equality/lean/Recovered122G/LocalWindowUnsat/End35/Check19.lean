import Recovered122G.LocalWindowUnsat.End35.Data19
import Recovered122G.LocalWindowUnsat.End35.Data20

/-! Kernel checks of segments 109-114 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok109 : check start109 proof109 = true := by
  decide +kernel

theorem ok110 : check start110 proof110 = true := by
  decide +kernel

theorem ok111 : check start111 proof111 = true := by
  decide +kernel

theorem ok112 : check start112 proof112 = true := by
  decide +kernel

theorem ok113 : check start113 proof113 = true := by
  decide +kernel

theorem ok114 : andB (check start114 proof114) (cpOk (replay start114 proof114) start115) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
