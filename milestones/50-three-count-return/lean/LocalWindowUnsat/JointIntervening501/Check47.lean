import LocalWindowUnsat.JointIntervening501.Data276
import LocalWindowUnsat.JointIntervening501.Data277
import LocalWindowUnsat.JointIntervening501.Data278
import LocalWindowUnsat.JointIntervening501.Data279
import LocalWindowUnsat.JointIntervening501.Data280
import LocalWindowUnsat.JointIntervening501.Data281
import LocalWindowUnsat.JointIntervening501.Data282

/-! Kernel checks of segments 277-282 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok277 : check start277 proof277 = true := by
  decide +kernel

theorem ok278 : check start278 proof278 = true := by
  decide +kernel

theorem ok279 : check start279 proof279 = true := by
  decide +kernel

theorem ok280 : andB (check start280 proof280) (cpOk (replay start280 proof280) start281) = true := by
  decide +kernel

theorem ok281 : check start281 proof281 = true := by
  decide +kernel

theorem ok282 : check start282 proof282 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
