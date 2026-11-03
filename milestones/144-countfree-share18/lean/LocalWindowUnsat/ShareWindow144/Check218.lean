import LocalWindowUnsat.ShareWindow144.Data218
import LocalWindowUnsat.ShareWindow144.Data219

/-! Kernel checks of segments 869-872 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok869 : check start869 proof869 = true := by
  decide +kernel

theorem ok870 : check start870 proof870 = true := by
  decide +kernel

theorem ok871 : check start871 proof871 = true := by
  decide +kernel

theorem ok872 : andB (check start872 proof872) (cpOk (replay start872 proof872) start873) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
