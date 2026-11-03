import LocalWindowUnsat.ShareWindow143.Data10
import LocalWindowUnsat.ShareWindow143.Data11

/-! Kernel checks of segments 37-40 of `share143` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow143
open Snake9.LratFast143
open Snake9.Lrat143 (Tree TreeTrue andB)

theorem ok37 : check start37 proof37 = true := by
  decide +kernel

theorem ok38 : check start38 proof38 = true := by
  decide +kernel

theorem ok39 : check start39 proof39 = true := by
  decide +kernel

theorem ok40 : andB (check start40 proof40) (cpOk (replay start40 proof40) start41) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow143
