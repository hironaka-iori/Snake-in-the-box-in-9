import LocalWindowUnsat.ShareWindow144.Data38
import LocalWindowUnsat.ShareWindow144.Data39

/-! Kernel checks of segments 149-152 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok149 : check start149 proof149 = true := by
  decide +kernel

theorem ok150 : check start150 proof150 = true := by
  decide +kernel

theorem ok151 : check start151 proof151 = true := by
  decide +kernel

theorem ok152 : andB (check start152 proof152) (cpOk (replay start152 proof152) start153) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
