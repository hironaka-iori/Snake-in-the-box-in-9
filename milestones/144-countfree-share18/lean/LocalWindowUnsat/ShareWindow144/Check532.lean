import LocalWindowUnsat.ShareWindow144.Data532
import LocalWindowUnsat.ShareWindow144.Data533

/-! Kernel checks of segments 2125-2128 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok2125 : check start2125 proof2125 = true := by
  decide +kernel

theorem ok2126 : check start2126 proof2126 = true := by
  decide +kernel

theorem ok2127 : check start2127 proof2127 = true := by
  decide +kernel

theorem ok2128 : andB (check start2128 proof2128) (cpOk (replay start2128 proof2128) start2129) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
