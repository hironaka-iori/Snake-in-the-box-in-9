import Refined111.LocalWindowUnsat.Middle325R.Data20
import Refined111.LocalWindowUnsat.Middle325R.Data21

/-! Kernel checks of segments 77-80 of `middle325r` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325R
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok77 : check start77 proof77 = true := by
  decide +kernel

theorem ok78 : check start78 proof78 = true := by
  decide +kernel

theorem ok79 : check start79 proof79 = true := by
  decide +kernel

theorem ok80 : andB (check start80 proof80) (cpOk (replay start80 proof80) start81) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325R
