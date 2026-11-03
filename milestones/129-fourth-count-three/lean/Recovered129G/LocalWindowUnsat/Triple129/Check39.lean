import Recovered129G.LocalWindowUnsat.Triple129.Data39
import Recovered129G.LocalWindowUnsat.Triple129.Data40

/-! Kernel checks of segments 153-156 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok153 : check start153 proof153 = true := by
  decide +kernel

theorem ok154 : check start154 proof154 = true := by
  decide +kernel

theorem ok155 : check start155 proof155 = true := by
  decide +kernel

theorem ok156 : andB (check start156 proof156) (cpOk (replay start156 proof156) start157) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
