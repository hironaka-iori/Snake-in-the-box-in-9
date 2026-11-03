import LocalWindowUnsat.ShareWindow144.Data553
import LocalWindowUnsat.ShareWindow144.Data554

/-! Kernel checks of segments 2209-2212 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2209 : check start2209 proof2209 = true := by
  decide +kernel

theorem ok2210 : check start2210 proof2210 = true := by
  decide +kernel

theorem ok2211 : check start2211 proof2211 = true := by
  decide +kernel

theorem ok2212 : andB (check start2212 proof2212) (cpOk (replay start2212 proof2212) start2213) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
