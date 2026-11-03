import LocalWindowUnsat.ShareWindow144.Data551
import LocalWindowUnsat.ShareWindow144.Data552

/-! Kernel checks of segments 2201-2204 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2201 : check start2201 proof2201 = true := by
  decide +kernel

theorem ok2202 : check start2202 proof2202 = true := by
  decide +kernel

theorem ok2203 : check start2203 proof2203 = true := by
  decide +kernel

theorem ok2204 : andB (check start2204 proof2204) (cpOk (replay start2204 proof2204) start2205) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
