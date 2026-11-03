import Recovered132G.LocalWindowUnsat.Endpoint132.Data24

/-! Kernel checks of segments 93-93 of `endpoint132` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Endpoint132
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok93 : andB (check start93 proof93) (hasEmpty (replay start93 proof93) 1024) = true := by
  decide +kernel

end Snake9.LocalWindow.Endpoint132
