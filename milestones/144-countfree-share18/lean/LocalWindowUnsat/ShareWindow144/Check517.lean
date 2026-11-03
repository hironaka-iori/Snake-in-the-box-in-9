import LocalWindowUnsat.ShareWindow144.Data517
import LocalWindowUnsat.ShareWindow144.Data518

/-! Kernel checks of segments 2065-2068 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2065 : check start2065 proof2065 = true := by
  decide +kernel

theorem ok2066 : check start2066 proof2066 = true := by
  decide +kernel

theorem ok2067 : check start2067 proof2067 = true := by
  decide +kernel

theorem ok2068 : andB (check start2068 proof2068) (cpOk (replay start2068 proof2068) start2069) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
