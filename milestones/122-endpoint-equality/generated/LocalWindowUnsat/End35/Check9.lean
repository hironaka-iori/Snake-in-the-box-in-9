import LocalWindowUnsat.End35.Data9
import LocalWindowUnsat.End35.Data10

/-! Kernel checks of segments 49-54 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok49 : check start49 proof49 = true := by
  decide +kernel

theorem ok50 : check start50 proof50 = true := by
  decide +kernel

theorem ok51 : check start51 proof51 = true := by
  decide +kernel

theorem ok52 : check start52 proof52 = true := by
  decide +kernel

theorem ok53 : check start53 proof53 = true := by
  decide +kernel

theorem ok54 : andB (check start54 proof54) (cpOk (replay start54 proof54) start55) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
