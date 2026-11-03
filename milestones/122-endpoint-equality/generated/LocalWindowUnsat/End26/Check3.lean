import LocalWindowUnsat.End26.Data3
import LocalWindowUnsat.End26.Data4

/-! Kernel checks of segments 13-18 of `end26` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End26
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok13 : check start13 proof13 = true := by
  decide +kernel

theorem ok14 : check start14 proof14 = true := by
  decide +kernel

theorem ok15 : check start15 proof15 = true := by
  decide +kernel

theorem ok16 : check start16 proof16 = true := by
  decide +kernel

theorem ok17 : check start17 proof17 = true := by
  decide +kernel

theorem ok18 : andB (check start18 proof18) (cpOk (replay start18 proof18) start19) = true := by
  decide +kernel

end Snake9.LocalWindow.End26
