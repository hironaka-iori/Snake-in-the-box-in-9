import Recovered129G.LocalWindowUnsat.Triple129.Data45
import Recovered129G.LocalWindowUnsat.Triple129.Data46

/-! Kernel checks of segments 177-180 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok177 : check start177 proof177 = true := by
  decide +kernel

theorem ok178 : check start178 proof178 = true := by
  decide +kernel

theorem ok179 : check start179 proof179 = true := by
  decide +kernel

theorem ok180 : andB (check start180 proof180) (cpOk (replay start180 proof180) start181) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
