import Recovered122G.LocalWindowUnsat.End35.Data25
import Recovered122G.LocalWindowUnsat.End35.Data26

/-! Kernel checks of segments 145-150 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok145 : check start145 proof145 = true := by
  decide +kernel

theorem ok146 : check start146 proof146 = true := by
  decide +kernel

theorem ok147 : check start147 proof147 = true := by
  decide +kernel

theorem ok148 : check start148 proof148 = true := by
  decide +kernel

theorem ok149 : check start149 proof149 = true := by
  decide +kernel

theorem ok150 : andB (check start150 proof150) (cpOk (replay start150 proof150) start151) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
