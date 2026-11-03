import LocalWindowUnsat.ShareWindow144.Data544
import LocalWindowUnsat.ShareWindow144.Data545

/-! Kernel checks of segments 2173-2176 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2173 : check start2173 proof2173 = true := by
  decide +kernel

theorem ok2174 : check start2174 proof2174 = true := by
  decide +kernel

theorem ok2175 : check start2175 proof2175 = true := by
  decide +kernel

theorem ok2176 : andB (check start2176 proof2176) (cpOk (replay start2176 proof2176) start2177) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
