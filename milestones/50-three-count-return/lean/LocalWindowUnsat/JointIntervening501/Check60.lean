import LocalWindowUnsat.JointIntervening501.Data354
import LocalWindowUnsat.JointIntervening501.Data355
import LocalWindowUnsat.JointIntervening501.Data356
import LocalWindowUnsat.JointIntervening501.Data357
import LocalWindowUnsat.JointIntervening501.Data358
import LocalWindowUnsat.JointIntervening501.Data359
import LocalWindowUnsat.JointIntervening501.Data360

/-! Kernel checks of segments 355-360 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok355 : check start355 proof355 = true := by
  decide +kernel

theorem ok356 : andB (check start356 proof356) (cpOk (replay start356 proof356) start357) = true := by
  decide +kernel

theorem ok357 : check start357 proof357 = true := by
  decide +kernel

theorem ok358 : check start358 proof358 = true := by
  decide +kernel

theorem ok359 : check start359 proof359 = true := by
  decide +kernel

theorem ok360 : andB (check start360 proof360) (hasEmpty (replay start360 proof360) 8192) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
