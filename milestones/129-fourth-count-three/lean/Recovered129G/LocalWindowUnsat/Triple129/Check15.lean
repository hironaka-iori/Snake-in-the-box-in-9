import Recovered129G.LocalWindowUnsat.Triple129.Data15
import Recovered129G.LocalWindowUnsat.Triple129.Data16

/-! Kernel checks of segments 57-60 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok57 : check start57 proof57 = true := by
  decide +kernel

theorem ok58 : check start58 proof58 = true := by
  decide +kernel

theorem ok59 : check start59 proof59 = true := by
  decide +kernel

theorem ok60 : andB (check start60 proof60) (cpOk (replay start60 proof60) start61) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
