import LocalWindowUnsat.ShareWindow144.Data232
import LocalWindowUnsat.ShareWindow144.Data233

/-! Kernel checks of segments 925-928 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok925 : check start925 proof925 = true := by
  decide +kernel

theorem ok926 : check start926 proof926 = true := by
  decide +kernel

theorem ok927 : check start927 proof927 = true := by
  decide +kernel

theorem ok928 : andB (check start928 proof928) (cpOk (replay start928 proof928) start929) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
