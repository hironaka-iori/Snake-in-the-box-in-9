import Refined112.LocalWindowUnsat.Sum3142.Data11
import Refined112.LocalWindowUnsat.Sum3142.Data12

/-! Kernel checks of segments 41-44 of `sum3142` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Sum3142
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok41 : check start41 proof41 = true := by
  decide +kernel

theorem ok42 : check start42 proof42 = true := by
  decide +kernel

theorem ok43 : check start43 proof43 = true := by
  decide +kernel

theorem ok44 : andB (check start44 proof44) (cpOk (replay start44 proof44) start45) = true := by
  decide +kernel

end Snake9.LocalWindow.Sum3142
