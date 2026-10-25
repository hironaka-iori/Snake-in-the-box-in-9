import LocalWindowUnsat.JointIntervening501.Data198
import LocalWindowUnsat.JointIntervening501.Data199
import LocalWindowUnsat.JointIntervening501.Data200
import LocalWindowUnsat.JointIntervening501.Data201
import LocalWindowUnsat.JointIntervening501.Data202
import LocalWindowUnsat.JointIntervening501.Data203
import LocalWindowUnsat.JointIntervening501.Data204

/-! Kernel checks of segments 199-204 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok199 : check start199 proof199 = true := by
  decide +kernel

theorem ok200 : andB (check start200 proof200) (cpOk (replay start200 proof200) start201) = true := by
  decide +kernel

theorem ok201 : check start201 proof201 = true := by
  decide +kernel

theorem ok202 : check start202 proof202 = true := by
  decide +kernel

theorem ok203 : check start203 proof203 = true := by
  decide +kernel

theorem ok204 : andB (check start204 proof204) (cpOk (replay start204 proof204) start205) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
