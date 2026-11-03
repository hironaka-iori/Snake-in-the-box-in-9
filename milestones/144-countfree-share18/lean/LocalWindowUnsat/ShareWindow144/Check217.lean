import LocalWindowUnsat.ShareWindow144.Data217
import LocalWindowUnsat.ShareWindow144.Data218

/-! Kernel checks of segments 865-868 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok865 : check start865 proof865 = true := by
  decide +kernel

theorem ok866 : check start866 proof866 = true := by
  decide +kernel

theorem ok867 : check start867 proof867 = true := by
  decide +kernel

theorem ok868 : andB (check start868 proof868) (cpOk (replay start868 proof868) start869) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
