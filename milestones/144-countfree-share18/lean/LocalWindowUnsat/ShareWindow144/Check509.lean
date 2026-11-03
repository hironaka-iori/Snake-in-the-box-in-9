import LocalWindowUnsat.ShareWindow144.Data509
import LocalWindowUnsat.ShareWindow144.Data510

/-! Kernel checks of segments 2033-2036 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2033 : check start2033 proof2033 = true := by
  decide +kernel

theorem ok2034 : check start2034 proof2034 = true := by
  decide +kernel

theorem ok2035 : check start2035 proof2035 = true := by
  decide +kernel

theorem ok2036 : andB (check start2036 proof2036) (cpOk (replay start2036 proof2036) start2037) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
