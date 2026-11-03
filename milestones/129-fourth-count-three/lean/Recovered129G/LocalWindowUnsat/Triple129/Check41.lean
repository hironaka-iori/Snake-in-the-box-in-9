import Recovered129G.LocalWindowUnsat.Triple129.Data41
import Recovered129G.LocalWindowUnsat.Triple129.Data42

/-! Kernel checks of segments 161-164 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok161 : check start161 proof161 = true := by
  decide +kernel

theorem ok162 : check start162 proof162 = true := by
  decide +kernel

theorem ok163 : check start163 proof163 = true := by
  decide +kernel

theorem ok164 : andB (check start164 proof164) (cpOk (replay start164 proof164) start165) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
