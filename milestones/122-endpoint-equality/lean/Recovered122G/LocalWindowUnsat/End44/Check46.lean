import Recovered122G.LocalWindowUnsat.End44.Data46
import Recovered122G.LocalWindowUnsat.End44.Data47

/-! Kernel checks of segments 271-276 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok271 : check start271 proof271 = true := by
  decide +kernel

theorem ok272 : check start272 proof272 = true := by
  decide +kernel

theorem ok273 : check start273 proof273 = true := by
  decide +kernel

theorem ok274 : check start274 proof274 = true := by
  decide +kernel

theorem ok275 : check start275 proof275 = true := by
  decide +kernel

theorem ok276 : andB (check start276 proof276) (cpOk (replay start276 proof276) start277) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
