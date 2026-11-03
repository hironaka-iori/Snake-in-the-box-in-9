import Recovered122G.LocalWindowUnsat.End26.Data10
import Recovered122G.LocalWindowUnsat.End26.Data11

/-! Kernel checks of segments 55-60 of `end26` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End26
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok55 : check start55 proof55 = true := by
  decide +kernel

theorem ok56 : check start56 proof56 = true := by
  decide +kernel

theorem ok57 : check start57 proof57 = true := by
  decide +kernel

theorem ok58 : check start58 proof58 = true := by
  decide +kernel

theorem ok59 : check start59 proof59 = true := by
  decide +kernel

theorem ok60 : andB (check start60 proof60) (cpOk (replay start60 proof60) start61) = true := by
  decide +kernel

end Snake9.LocalWindow.End26
