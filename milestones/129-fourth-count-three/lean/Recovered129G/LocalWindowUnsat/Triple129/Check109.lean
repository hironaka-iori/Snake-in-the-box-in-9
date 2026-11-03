import Recovered129G.LocalWindowUnsat.Triple129.Data109

/-! Kernel checks of segments 433-435 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok433 : check start433 proof433 = true := by
  decide +kernel

theorem ok434 : check start434 proof434 = true := by
  decide +kernel

theorem ok435 : andB (check start435 proof435) (hasEmpty (replay start435 proof435) 4096) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
