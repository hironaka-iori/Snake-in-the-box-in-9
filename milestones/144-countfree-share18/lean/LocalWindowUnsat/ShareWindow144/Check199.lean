import LocalWindowUnsat.ShareWindow144.Data199
import LocalWindowUnsat.ShareWindow144.Data200

/-! Kernel checks of segments 793-796 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok793 : check start793 proof793 = true := by
  decide +kernel

theorem ok794 : check start794 proof794 = true := by
  decide +kernel

theorem ok795 : check start795 proof795 = true := by
  decide +kernel

theorem ok796 : andB (check start796 proof796) (cpOk (replay start796 proof796) start797) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
