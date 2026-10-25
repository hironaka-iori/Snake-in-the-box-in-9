import LocalWindowUnsat.JointIntervening501.Data150
import LocalWindowUnsat.JointIntervening501.Data151
import LocalWindowUnsat.JointIntervening501.Data152
import LocalWindowUnsat.JointIntervening501.Data153
import LocalWindowUnsat.JointIntervening501.Data154
import LocalWindowUnsat.JointIntervening501.Data155
import LocalWindowUnsat.JointIntervening501.Data156

/-! Kernel checks of segments 151-156 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok151 : check start151 proof151 = true := by
  decide +kernel

theorem ok152 : andB (check start152 proof152) (cpOk (replay start152 proof152) start153) = true := by
  decide +kernel

theorem ok153 : check start153 proof153 = true := by
  decide +kernel

theorem ok154 : check start154 proof154 = true := by
  decide +kernel

theorem ok155 : check start155 proof155 = true := by
  decide +kernel

theorem ok156 : andB (check start156 proof156) (cpOk (replay start156 proof156) start157) = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
