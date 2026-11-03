import Recovered129G.LocalWindowUnsat.Triple129.Data80
import Recovered129G.LocalWindowUnsat.Triple129.Data81

/-! Kernel checks of segments 317-320 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok317 : check start317 proof317 = true := by
  decide +kernel

theorem ok318 : check start318 proof318 = true := by
  decide +kernel

theorem ok319 : check start319 proof319 = true := by
  decide +kernel

theorem ok320 : andB (check start320 proof320) (cpOk (replay start320 proof320) start321) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
