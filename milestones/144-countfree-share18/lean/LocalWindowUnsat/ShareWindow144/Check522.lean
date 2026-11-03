import LocalWindowUnsat.ShareWindow144.Data522
import LocalWindowUnsat.ShareWindow144.Data523

/-! Kernel checks of segments 2085-2088 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2085 : check start2085 proof2085 = true := by
  decide +kernel

theorem ok2086 : check start2086 proof2086 = true := by
  decide +kernel

theorem ok2087 : check start2087 proof2087 = true := by
  decide +kernel

theorem ok2088 : andB (check start2088 proof2088) (cpOk (replay start2088 proof2088) start2089) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
