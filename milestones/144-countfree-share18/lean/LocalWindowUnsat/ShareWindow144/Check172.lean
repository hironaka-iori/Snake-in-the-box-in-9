import LocalWindowUnsat.ShareWindow144.Data172
import LocalWindowUnsat.ShareWindow144.Data173

/-! Kernel checks of segments 685-688 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok685 : check start685 proof685 = true := by
  decide +kernel

theorem ok686 : check start686 proof686 = true := by
  decide +kernel

theorem ok687 : check start687 proof687 = true := by
  decide +kernel

theorem ok688 : andB (check start688 proof688) (cpOk (replay start688 proof688) start689) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
