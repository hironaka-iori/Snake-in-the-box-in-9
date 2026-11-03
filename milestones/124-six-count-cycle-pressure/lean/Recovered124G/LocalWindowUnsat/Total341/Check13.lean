import Recovered124G.LocalWindowUnsat.Total341.Data13
import Recovered124G.LocalWindowUnsat.Total341.Data14

/-! Kernel checks of segments 49-52 of `total341` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Total341
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok49 : check start49 proof49 = true := by
  decide +kernel

theorem ok50 : check start50 proof50 = true := by
  decide +kernel

theorem ok51 : check start51 proof51 = true := by
  decide +kernel

theorem ok52 : andB (check start52 proof52) (cpOk (replay start52 proof52) start53) = true := by
  decide +kernel

end Snake9.LocalWindow.Total341
