import LocalWindowUnsat.Middle325.Data189
import LocalWindowUnsat.Middle325.Data190

/-! Kernel checks of segments 190-190 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok190 : andB (check start190 proof190) (cpOk (replay start190 proof190) start191) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
