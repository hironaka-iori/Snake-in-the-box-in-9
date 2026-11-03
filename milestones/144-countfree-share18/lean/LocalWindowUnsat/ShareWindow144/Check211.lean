import LocalWindowUnsat.ShareWindow144.Data211
import LocalWindowUnsat.ShareWindow144.Data212

/-! Kernel checks of segments 841-844 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok841 : check start841 proof841 = true := by
  decide +kernel

theorem ok842 : check start842 proof842 = true := by
  decide +kernel

theorem ok843 : check start843 proof843 = true := by
  decide +kernel

theorem ok844 : andB (check start844 proof844) (cpOk (replay start844 proof844) start845) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
