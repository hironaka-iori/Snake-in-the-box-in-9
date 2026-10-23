import LocalWindowUnsat.FourRun0.Data48
import LocalWindowUnsat.FourRun0.Data49
import LocalWindowUnsat.FourRun0.Data50
import LocalWindowUnsat.FourRun0.Data51
import LocalWindowUnsat.FourRun0.Data52
import LocalWindowUnsat.FourRun0.Data53
import LocalWindowUnsat.FourRun0.Data54

/-! Kernel checks of segments 49-54 of `four0` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.FourRun0
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

theorem ok53 : check start53 proof53 = true := by
  decide +kernel

theorem ok54 : check start54 proof54 = true := by
  decide +kernel

end Snake9.LocalWindow.FourRun0
