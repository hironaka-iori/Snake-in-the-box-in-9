import LocalWindowUnsat.ShareWindow144.Data39
import LocalWindowUnsat.ShareWindow144.Data40

/-! Kernel checks of segments 153-156 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok153 : check start153 proof153 = true := by
  decide +kernel

theorem ok154 : check start154 proof154 = true := by
  decide +kernel

theorem ok155 : check start155 proof155 = true := by
  decide +kernel

theorem ok156 : andB (check start156 proof156) (cpOk (replay start156 proof156) start157) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
