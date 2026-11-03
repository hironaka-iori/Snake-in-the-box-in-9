import LocalWindowUnsat.End44.Data18
import LocalWindowUnsat.End44.Data19

/-! Kernel checks of segments 103-108 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok103 : check start103 proof103 = true := by
  decide +kernel

theorem ok104 : check start104 proof104 = true := by
  decide +kernel

theorem ok105 : check start105 proof105 = true := by
  decide +kernel

theorem ok106 : check start106 proof106 = true := by
  decide +kernel

theorem ok107 : check start107 proof107 = true := by
  decide +kernel

theorem ok108 : andB (check start108 proof108) (cpOk (replay start108 proof108) start109) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
