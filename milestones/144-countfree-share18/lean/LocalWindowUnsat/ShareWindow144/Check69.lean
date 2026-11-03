import LocalWindowUnsat.ShareWindow144.Data69
import LocalWindowUnsat.ShareWindow144.Data70

/-! Kernel checks of segments 273-276 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok273 : check start273 proof273 = true := by
  decide +kernel

theorem ok274 : check start274 proof274 = true := by
  decide +kernel

theorem ok275 : check start275 proof275 = true := by
  decide +kernel

theorem ok276 : andB (check start276 proof276) (cpOk (replay start276 proof276) start277) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
