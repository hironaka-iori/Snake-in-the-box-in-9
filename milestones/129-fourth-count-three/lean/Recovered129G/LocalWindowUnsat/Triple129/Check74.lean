import Recovered129G.LocalWindowUnsat.Triple129.Data74
import Recovered129G.LocalWindowUnsat.Triple129.Data75

/-! Kernel checks of segments 293-296 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok293 : check start293 proof293 = true := by
  decide +kernel

theorem ok294 : check start294 proof294 = true := by
  decide +kernel

theorem ok295 : check start295 proof295 = true := by
  decide +kernel

theorem ok296 : andB (check start296 proof296) (cpOk (replay start296 proof296) start297) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
