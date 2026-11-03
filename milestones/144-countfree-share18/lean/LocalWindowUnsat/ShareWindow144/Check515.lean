import LocalWindowUnsat.ShareWindow144.Data515
import LocalWindowUnsat.ShareWindow144.Data516

/-! Kernel checks of segments 2057-2060 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2057 : check start2057 proof2057 = true := by
  decide +kernel

theorem ok2058 : check start2058 proof2058 = true := by
  decide +kernel

theorem ok2059 : check start2059 proof2059 = true := by
  decide +kernel

theorem ok2060 : andB (check start2060 proof2060) (cpOk (replay start2060 proof2060) start2061) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
