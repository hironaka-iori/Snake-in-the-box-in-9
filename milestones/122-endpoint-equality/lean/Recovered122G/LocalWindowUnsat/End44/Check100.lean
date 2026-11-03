import Recovered122G.LocalWindowUnsat.End44.Data100
import Recovered122G.LocalWindowUnsat.End44.Data101

/-! Kernel checks of segments 595-600 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok595 : check start595 proof595 = true := by
  decide +kernel

theorem ok596 : check start596 proof596 = true := by
  decide +kernel

theorem ok597 : check start597 proof597 = true := by
  decide +kernel

theorem ok598 : check start598 proof598 = true := by
  decide +kernel

theorem ok599 : check start599 proof599 = true := by
  decide +kernel

theorem ok600 : andB (check start600 proof600) (cpOk (replay start600 proof600) start601) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
