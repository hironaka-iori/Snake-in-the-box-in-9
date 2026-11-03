import LocalWindowUnsat.SixFour10.Data33
import LocalWindowUnsat.SixFour10.Data34

/-! Kernel checks of segments 193-198 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok193 : check start193 proof193 = true := by
  decide +kernel

theorem ok194 : check start194 proof194 = true := by
  decide +kernel

theorem ok195 : check start195 proof195 = true := by
  decide +kernel

theorem ok196 : check start196 proof196 = true := by
  decide +kernel

theorem ok197 : check start197 proof197 = true := by
  decide +kernel

theorem ok198 : andB (check start198 proof198) (cpOk (replay start198 proof198) start199) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
