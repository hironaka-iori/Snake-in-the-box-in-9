import Recovered129G.LocalWindowUnsat.Triple129.Data86
import Recovered129G.LocalWindowUnsat.Triple129.Data87

/-! Kernel checks of segments 341-344 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok341 : check start341 proof341 = true := by
  decide +kernel

theorem ok342 : check start342 proof342 = true := by
  decide +kernel

theorem ok343 : check start343 proof343 = true := by
  decide +kernel

theorem ok344 : andB (check start344 proof344) (cpOk (replay start344 proof344) start345) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
