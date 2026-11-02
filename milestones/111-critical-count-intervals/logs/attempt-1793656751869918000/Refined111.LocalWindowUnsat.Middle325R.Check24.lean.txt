import Refined111.LocalWindowUnsat.Middle325R.Data24
import Refined111.LocalWindowUnsat.Middle325R.Data25

/-! Kernel checks of segments 93-96 of `middle325r` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325R
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok93 : check start93 proof93 = true := by
  decide +kernel

theorem ok94 : check start94 proof94 = true := by
  decide +kernel

theorem ok95 : check start95 proof95 = true := by
  decide +kernel

theorem ok96 : andB (check start96 proof96) (cpOk (replay start96 proof96) start97) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325R
