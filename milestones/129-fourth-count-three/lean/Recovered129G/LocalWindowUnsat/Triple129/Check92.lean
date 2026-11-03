import Recovered129G.LocalWindowUnsat.Triple129.Data92
import Recovered129G.LocalWindowUnsat.Triple129.Data93

/-! Kernel checks of segments 365-368 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok365 : check start365 proof365 = true := by
  decide +kernel

theorem ok366 : check start366 proof366 = true := by
  decide +kernel

theorem ok367 : check start367 proof367 = true := by
  decide +kernel

theorem ok368 : andB (check start368 proof368) (cpOk (replay start368 proof368) start369) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
