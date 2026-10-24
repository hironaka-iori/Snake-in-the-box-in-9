import LocalWindowUnsat.CycleWindow401.Data36
import LocalWindowUnsat.CycleWindow401.Data37
import LocalWindowUnsat.CycleWindow401.Data38

/-! Kernel checks of segments 37-38 of `cycle401` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleWindow401
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok37 : check start37 proof37 = true := by
  decide +kernel

theorem ok38 : andB (check start38 proof38) (hasEmpty (replay start38 proof38) 2048) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleWindow401
