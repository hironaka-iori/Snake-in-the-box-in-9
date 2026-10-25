import LocalWindowUnsat.JointIntervening501.Data204
import LocalWindowUnsat.JointIntervening501.Data205
import LocalWindowUnsat.JointIntervening501.Data206
import LocalWindowUnsat.JointIntervening501.Data207
import LocalWindowUnsat.JointIntervening501.Data208
import LocalWindowUnsat.JointIntervening501.Data209
import LocalWindowUnsat.JointIntervening501.Data210

/-! Kernel checks of segments 205-210 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok205 : check start205 proof205 = true := by
  decide +kernel

theorem ok206 : check start206 proof206 = true := by
  decide +kernel

theorem ok207 : check start207 proof207 = true := by
  decide +kernel

theorem ok208 : andB (check start208 proof208) (cpOk (replay start208 proof208) start209) = true := by
  decide +kernel

theorem ok209 : check start209 proof209 = true := by
  decide +kernel

theorem ok210 : check start210 proof210 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
