import LocalWindowUnsat.ShareWindow144.Data554
import LocalWindowUnsat.ShareWindow144.Data555

/-! Kernel checks of segments 2213-2216 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2213 : check start2213 proof2213 = true := by
  decide +kernel

theorem ok2214 : check start2214 proof2214 = true := by
  decide +kernel

theorem ok2215 : check start2215 proof2215 = true := by
  decide +kernel

theorem ok2216 : andB (check start2216 proof2216) (cpOk (replay start2216 proof2216) start2217) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
