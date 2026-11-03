import Recovered122G.LocalWindowUnsat.End44.Data63
import Recovered122G.LocalWindowUnsat.End44.Data64

/-! Kernel checks of segments 373-378 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok373 : check start373 proof373 = true := by
  decide +kernel

theorem ok374 : check start374 proof374 = true := by
  decide +kernel

theorem ok375 : check start375 proof375 = true := by
  decide +kernel

theorem ok376 : check start376 proof376 = true := by
  decide +kernel

theorem ok377 : check start377 proof377 = true := by
  decide +kernel

theorem ok378 : andB (check start378 proof378) (cpOk (replay start378 proof378) start379) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
