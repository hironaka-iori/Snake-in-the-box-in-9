import LocalWindowUnsat.ShareWindow144.Data51
import LocalWindowUnsat.ShareWindow144.Data52

/-! Kernel checks of segments 201-204 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok201 : check start201 proof201 = true := by
  decide +kernel

theorem ok202 : check start202 proof202 = true := by
  decide +kernel

theorem ok203 : check start203 proof203 = true := by
  decide +kernel

theorem ok204 : andB (check start204 proof204) (cpOk (replay start204 proof204) start205) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
