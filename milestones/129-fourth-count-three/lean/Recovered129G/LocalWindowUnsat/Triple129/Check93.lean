import Recovered129G.LocalWindowUnsat.Triple129.Data93
import Recovered129G.LocalWindowUnsat.Triple129.Data94

/-! Kernel checks of segments 369-372 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok369 : check start369 proof369 = true := by
  decide +kernel

theorem ok370 : check start370 proof370 = true := by
  decide +kernel

theorem ok371 : check start371 proof371 = true := by
  decide +kernel

theorem ok372 : andB (check start372 proof372) (cpOk (replay start372 proof372) start373) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
