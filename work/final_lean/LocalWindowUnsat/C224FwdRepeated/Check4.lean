import LocalWindowUnsat.C224FwdRepeated.Data16

/-! Kernel checks of segments 13-16 of `224_fwd_repeated` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.C224FwdRepeated
open Snake9.Lrat

theorem ok13 : check start13 proof13 = true := by
  decide +kernel

theorem ok14 : check start14 proof14 = true := by
  decide +kernel

theorem ok15 : andB (check start15 proof15) (cpOk (replay start15 proof15) cp16) = true := by
  decide +kernel

theorem ok16 : check start16 proof16 = true := by
  decide +kernel

end Snake9.LocalWindow.C224FwdRepeated
