import LocalWindowUnsat.Middle325.Data181
import LocalWindowUnsat.Middle325.Data182

/-! Kernel checks of segments 182-182 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok182 : andB (check start182 proof182) (cpOk (replay start182 proof182) start183) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
