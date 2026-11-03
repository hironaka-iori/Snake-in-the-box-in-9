import Recovered129G.LocalWindowUnsat.Triple129.Data49
import Recovered129G.LocalWindowUnsat.Triple129.Data50

/-! Kernel checks of segments 193-196 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok193 : check start193 proof193 = true := by
  decide +kernel

theorem ok194 : check start194 proof194 = true := by
  decide +kernel

theorem ok195 : check start195 proof195 = true := by
  decide +kernel

theorem ok196 : andB (check start196 proof196) (cpOk (replay start196 proof196) start197) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
