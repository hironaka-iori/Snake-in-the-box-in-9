import LocalWindowUnsat.Middle325R.Data6
import LocalWindowUnsat.Middle325R.Data7

/-! Kernel checks of segments 21-24 of `middle325r` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325R
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok21 : check start21 proof21 = true := by
  decide +kernel

theorem ok22 : check start22 proof22 = true := by
  decide +kernel

theorem ok23 : check start23 proof23 = true := by
  decide +kernel

theorem ok24 : andB (check start24 proof24) (cpOk (replay start24 proof24) start25) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325R
