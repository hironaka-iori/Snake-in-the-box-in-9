import LocalWindowUnsat.ShareWindow144.Data538
import LocalWindowUnsat.ShareWindow144.Data539

/-! Kernel checks of segments 2149-2152 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2149 : check start2149 proof2149 = true := by
  decide +kernel

theorem ok2150 : check start2150 proof2150 = true := by
  decide +kernel

theorem ok2151 : check start2151 proof2151 = true := by
  decide +kernel

theorem ok2152 : andB (check start2152 proof2152) (cpOk (replay start2152 proof2152) start2153) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
