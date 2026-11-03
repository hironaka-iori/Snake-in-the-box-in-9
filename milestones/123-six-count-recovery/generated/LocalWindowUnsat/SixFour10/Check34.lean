import LocalWindowUnsat.SixFour10.Data34
import LocalWindowUnsat.SixFour10.Data35

/-! Kernel checks of segments 199-204 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok199 : check start199 proof199 = true := by
  decide +kernel

theorem ok200 : check start200 proof200 = true := by
  decide +kernel

theorem ok201 : check start201 proof201 = true := by
  decide +kernel

theorem ok202 : check start202 proof202 = true := by
  decide +kernel

theorem ok203 : check start203 proof203 = true := by
  decide +kernel

theorem ok204 : andB (check start204 proof204) (cpOk (replay start204 proof204) start205) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
