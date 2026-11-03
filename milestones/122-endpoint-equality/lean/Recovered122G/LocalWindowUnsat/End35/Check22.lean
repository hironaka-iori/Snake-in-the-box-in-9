import Recovered122G.LocalWindowUnsat.End35.Data22
import Recovered122G.LocalWindowUnsat.End35.Data23

/-! Kernel checks of segments 127-132 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok127 : check start127 proof127 = true := by
  decide +kernel

theorem ok128 : check start128 proof128 = true := by
  decide +kernel

theorem ok129 : check start129 proof129 = true := by
  decide +kernel

theorem ok130 : check start130 proof130 = true := by
  decide +kernel

theorem ok131 : check start131 proof131 = true := by
  decide +kernel

theorem ok132 : andB (check start132 proof132) (cpOk (replay start132 proof132) start133) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
