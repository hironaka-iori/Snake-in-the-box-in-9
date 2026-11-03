import LocalWindowUnsat.ShareWindow144.Data234
import LocalWindowUnsat.ShareWindow144.Data235

/-! Kernel checks of segments 933-936 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok933 : check start933 proof933 = true := by
  decide +kernel

theorem ok934 : check start934 proof934 = true := by
  decide +kernel

theorem ok935 : check start935 proof935 = true := by
  decide +kernel

theorem ok936 : andB (check start936 proof936) (cpOk (replay start936 proof936) start937) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
