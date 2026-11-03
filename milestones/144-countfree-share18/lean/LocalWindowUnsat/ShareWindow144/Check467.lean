import LocalWindowUnsat.ShareWindow144.Data467
import LocalWindowUnsat.ShareWindow144.Data468

/-! Kernel checks of segments 1865-1868 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1865 : check start1865 proof1865 = true := by
  decide +kernel

theorem ok1866 : check start1866 proof1866 = true := by
  decide +kernel

theorem ok1867 : check start1867 proof1867 = true := by
  decide +kernel

theorem ok1868 : andB (check start1868 proof1868) (cpOk (replay start1868 proof1868) start1869) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
