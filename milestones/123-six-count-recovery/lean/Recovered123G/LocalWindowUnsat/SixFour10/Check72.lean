import Recovered123G.LocalWindowUnsat.SixFour10.Data72
import Recovered123G.LocalWindowUnsat.SixFour10.Data73

/-! Kernel checks of segments 427-432 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok427 : check start427 proof427 = true := by
  decide +kernel

theorem ok428 : check start428 proof428 = true := by
  decide +kernel

theorem ok429 : check start429 proof429 = true := by
  decide +kernel

theorem ok430 : check start430 proof430 = true := by
  decide +kernel

theorem ok431 : check start431 proof431 = true := by
  decide +kernel

theorem ok432 : andB (check start432 proof432) (cpOk (replay start432 proof432) start433) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
