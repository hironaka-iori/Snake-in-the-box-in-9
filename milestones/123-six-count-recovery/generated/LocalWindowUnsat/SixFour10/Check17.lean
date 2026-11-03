import LocalWindowUnsat.SixFour10.Data17
import LocalWindowUnsat.SixFour10.Data18

/-! Kernel checks of segments 97-102 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok97 : check start97 proof97 = true := by
  decide +kernel

theorem ok98 : check start98 proof98 = true := by
  decide +kernel

theorem ok99 : check start99 proof99 = true := by
  decide +kernel

theorem ok100 : check start100 proof100 = true := by
  decide +kernel

theorem ok101 : check start101 proof101 = true := by
  decide +kernel

theorem ok102 : andB (check start102 proof102) (cpOk (replay start102 proof102) start103) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
