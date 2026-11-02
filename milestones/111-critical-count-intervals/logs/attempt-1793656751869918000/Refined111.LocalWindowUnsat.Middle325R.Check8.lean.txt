import Refined111.LocalWindowUnsat.Middle325R.Data8
import Refined111.LocalWindowUnsat.Middle325R.Data9

/-! Kernel checks of segments 29-32 of `middle325r` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325R
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok29 : check start29 proof29 = true := by
  decide +kernel

theorem ok30 : check start30 proof30 = true := by
  decide +kernel

theorem ok31 : check start31 proof31 = true := by
  decide +kernel

theorem ok32 : andB (check start32 proof32) (cpOk (replay start32 proof32) start33) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325R
