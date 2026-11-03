import LocalWindowUnsat.ShareWindow144.Data546
import LocalWindowUnsat.ShareWindow144.Data547

/-! Kernel checks of segments 2181-2184 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2181 : check start2181 proof2181 = true := by
  decide +kernel

theorem ok2182 : check start2182 proof2182 = true := by
  decide +kernel

theorem ok2183 : check start2183 proof2183 = true := by
  decide +kernel

theorem ok2184 : andB (check start2184 proof2184) (cpOk (replay start2184 proof2184) start2185) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
