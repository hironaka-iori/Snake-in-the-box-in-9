import Recovered122G.LocalWindowUnsat.End35.Data70
import Recovered122G.LocalWindowUnsat.End35.Data71

/-! Kernel checks of segments 415-420 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok415 : check start415 proof415 = true := by
  decide +kernel

theorem ok416 : check start416 proof416 = true := by
  decide +kernel

theorem ok417 : check start417 proof417 = true := by
  decide +kernel

theorem ok418 : check start418 proof418 = true := by
  decide +kernel

theorem ok419 : check start419 proof419 = true := by
  decide +kernel

theorem ok420 : andB (check start420 proof420) (cpOk (replay start420 proof420) start421) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
