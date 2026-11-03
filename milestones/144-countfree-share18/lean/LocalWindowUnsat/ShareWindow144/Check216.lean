import LocalWindowUnsat.ShareWindow144.Data216
import LocalWindowUnsat.ShareWindow144.Data217

/-! Kernel checks of segments 861-864 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok861 : check start861 proof861 = true := by
  decide +kernel

theorem ok862 : check start862 proof862 = true := by
  decide +kernel

theorem ok863 : check start863 proof863 = true := by
  decide +kernel

theorem ok864 : andB (check start864 proof864) (cpOk (replay start864 proof864) start865) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
