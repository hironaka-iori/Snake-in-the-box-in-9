import LocalWindowUnsat.Middle325R.Data3
import LocalWindowUnsat.Middle325R.Data4

/-! Kernel checks of segments 9-12 of `middle325r` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325R
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok9 : check start9 proof9 = true := by
  decide +kernel

theorem ok10 : check start10 proof10 = true := by
  decide +kernel

theorem ok11 : check start11 proof11 = true := by
  decide +kernel

theorem ok12 : andB (check start12 proof12) (cpOk (replay start12 proof12) start13) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325R
