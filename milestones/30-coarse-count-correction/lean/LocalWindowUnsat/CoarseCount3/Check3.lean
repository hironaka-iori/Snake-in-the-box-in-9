import LocalWindowUnsat.CoarseCount3.Data12
import LocalWindowUnsat.CoarseCount3.Data13
import LocalWindowUnsat.CoarseCount3.Data14
import LocalWindowUnsat.CoarseCount3.Data15
import LocalWindowUnsat.CoarseCount3.Data16
import LocalWindowUnsat.CoarseCount3.Data17

/-! Kernel checks of segments 13-17 of `coarse3` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CoarseCount3
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok13 : check start13 proof13 = true := by
  decide +kernel

theorem ok14 : check start14 proof14 = true := by
  decide +kernel

theorem ok15 : check start15 proof15 = true := by
  decide +kernel

theorem ok16 : andB (check start16 proof16) (cpOk (replay start16 proof16) start17) = true := by
  decide +kernel

theorem ok17 : andB (check start17 proof17) (hasEmpty (replay start17 proof17) 2048) = true := by
  decide +kernel

end Snake9.LocalWindow.CoarseCount3
