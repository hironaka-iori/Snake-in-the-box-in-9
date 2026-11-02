import Recovered111.LocalWindowUnsat.Middle325.Data115
import Recovered111.LocalWindowUnsat.Middle325.Data116

/-! Kernel checks of segments 116-116 of `middle325` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Middle325
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok116 : andB (check start116 proof116) (cpOk (replay start116 proof116) start117) = true := by
  decide +kernel

end Snake9.LocalWindow.Middle325
