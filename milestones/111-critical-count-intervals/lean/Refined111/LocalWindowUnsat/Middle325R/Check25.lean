import Refined111.LocalWindowUnsat.Middle325R.Data25
import Refined111.LocalWindowUnsat.Middle325R.Data26

/-! Kernel checks of segments 97-100 of `middle325r` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325R
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok97 : check start97 proof97 = true := by
  decide +kernel

theorem ok98 : check start98 proof98 = true := by
  decide +kernel

theorem ok99 : check start99 proof99 = true := by
  decide +kernel

theorem ok100 : andB (check start100 proof100) (cpOk (replay start100 proof100) start101) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325R
