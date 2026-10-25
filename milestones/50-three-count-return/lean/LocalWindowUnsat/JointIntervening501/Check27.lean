import LocalWindowUnsat.JointIntervening501.Data156
import LocalWindowUnsat.JointIntervening501.Data157
import LocalWindowUnsat.JointIntervening501.Data158
import LocalWindowUnsat.JointIntervening501.Data159
import LocalWindowUnsat.JointIntervening501.Data160
import LocalWindowUnsat.JointIntervening501.Data161
import LocalWindowUnsat.JointIntervening501.Data162

/-! Kernel checks of segments 157-162 of `sum501` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.JointIntervening501
open Snake9.LratFast14
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok157 : check start157 proof157 = true := by
  decide +kernel

theorem ok158 : check start158 proof158 = true := by
  decide +kernel

theorem ok159 : check start159 proof159 = true := by
  decide +kernel

theorem ok160 : andB (check start160 proof160) (cpOk (replay start160 proof160) start161) = true := by
  decide +kernel

theorem ok161 : check start161 proof161 = true := by
  decide +kernel

theorem ok162 : check start162 proof162 = true := by
  decide +kernel

end Snake9.LocalWindow.JointIntervening501
