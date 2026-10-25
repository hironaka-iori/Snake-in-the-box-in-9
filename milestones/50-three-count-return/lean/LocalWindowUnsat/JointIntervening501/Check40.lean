import LocalWindowUnsat.JointIntervening501.Data234
import LocalWindowUnsat.JointIntervening501.Data235
import LocalWindowUnsat.JointIntervening501.Data236
import LocalWindowUnsat.JointIntervening501.Data237
import LocalWindowUnsat.JointIntervening501.Data238
import LocalWindowUnsat.JointIntervening501.Data239
import LocalWindowUnsat.JointIntervening501.Data240

/-! Kernel checks of segments 235-240 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok235 : check start235 proof235 = true := by
  decide +kernel

theorem ok236 : andB (check start236 proof236) (cpOk (replay start236 proof236) start237) = true := by
  decide +kernel

theorem ok237 : check start237 proof237 = true := by
  decide +kernel

theorem ok238 : check start238 proof238 = true := by
  decide +kernel

theorem ok239 : check start239 proof239 = true := by
  decide +kernel

theorem ok240 : andB (check start240 proof240) (cpOk (replay start240 proof240) start241) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
