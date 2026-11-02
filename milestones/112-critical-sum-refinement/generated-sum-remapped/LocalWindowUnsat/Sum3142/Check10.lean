import LocalWindowUnsat.Sum3142.Data10
import LocalWindowUnsat.Sum3142.Data11

/-! Kernel checks of segments 37-40 of `sum3142` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Sum3142
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok37 : check start37 proof37 = true := by
  decide +kernel

theorem ok38 : check start38 proof38 = true := by
  decide +kernel

theorem ok39 : check start39 proof39 = true := by
  decide +kernel

theorem ok40 : andB (check start40 proof40) (cpOk (replay start40 proof40) start41) = true := by
  decide +kernel

end Snake9.LocalWindow.Sum3142
