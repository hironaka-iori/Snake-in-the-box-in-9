import Recovered122G.LocalWindowUnsat.End44.Data4
import Recovered122G.LocalWindowUnsat.End44.Data5

/-! Kernel checks of segments 19-24 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok19 : check start19 proof19 = true := by
  decide +kernel

theorem ok20 : check start20 proof20 = true := by
  decide +kernel

theorem ok21 : check start21 proof21 = true := by
  decide +kernel

theorem ok22 : check start22 proof22 = true := by
  decide +kernel

theorem ok23 : check start23 proof23 = true := by
  decide +kernel

theorem ok24 : andB (check start24 proof24) (cpOk (replay start24 proof24) start25) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
