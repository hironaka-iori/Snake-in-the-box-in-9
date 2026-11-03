import Recovered122G.LocalWindowUnsat.End44.Data44
import Recovered122G.LocalWindowUnsat.End44.Data45

/-! Kernel checks of segments 259-264 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok259 : check start259 proof259 = true := by
  decide +kernel

theorem ok260 : check start260 proof260 = true := by
  decide +kernel

theorem ok261 : check start261 proof261 = true := by
  decide +kernel

theorem ok262 : check start262 proof262 = true := by
  decide +kernel

theorem ok263 : check start263 proof263 = true := by
  decide +kernel

theorem ok264 : andB (check start264 proof264) (cpOk (replay start264 proof264) start265) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
