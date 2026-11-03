import Recovered123G.LocalWindowUnsat.SixFour10.Data11
import Recovered123G.LocalWindowUnsat.SixFour10.Data12

/-! Kernel checks of segments 61-66 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok61 : check start61 proof61 = true := by
  decide +kernel

theorem ok62 : check start62 proof62 = true := by
  decide +kernel

theorem ok63 : check start63 proof63 = true := by
  decide +kernel

theorem ok64 : check start64 proof64 = true := by
  decide +kernel

theorem ok65 : check start65 proof65 = true := by
  decide +kernel

theorem ok66 : andB (check start66 proof66) (cpOk (replay start66 proof66) start67) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
