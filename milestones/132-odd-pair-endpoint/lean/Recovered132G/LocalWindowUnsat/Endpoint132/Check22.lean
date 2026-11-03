import Recovered132G.LocalWindowUnsat.Endpoint132.Data22
import Recovered132G.LocalWindowUnsat.Endpoint132.Data23

/-! Kernel checks of segments 85-88 of `endpoint132` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Endpoint132
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok85 : check start85 proof85 = true := by
  decide +kernel

theorem ok86 : check start86 proof86 = true := by
  decide +kernel

theorem ok87 : check start87 proof87 = true := by
  decide +kernel

theorem ok88 : andB (check start88 proof88) (cpOk (replay start88 proof88) start89) = true := by
  decide +kernel

end Snake9.LocalWindow.Endpoint132
