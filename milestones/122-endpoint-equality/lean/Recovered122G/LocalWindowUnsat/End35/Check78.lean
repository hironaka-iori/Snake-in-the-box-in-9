import Recovered122G.LocalWindowUnsat.End35.Data78
import Recovered122G.LocalWindowUnsat.End35.Data79

/-! Kernel checks of segments 463-468 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok463 : check start463 proof463 = true := by
  decide +kernel

theorem ok464 : check start464 proof464 = true := by
  decide +kernel

theorem ok465 : check start465 proof465 = true := by
  decide +kernel

theorem ok466 : check start466 proof466 = true := by
  decide +kernel

theorem ok467 : check start467 proof467 = true := by
  decide +kernel

theorem ok468 : andB (check start468 proof468) (cpOk (replay start468 proof468) start469) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
