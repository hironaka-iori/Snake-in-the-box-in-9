import LocalWindowUnsat.CycleBase140.Data40
import LocalWindowUnsat.CycleBase140.Data41

/-! Kernel checks of segments 157-160 of `base140` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.CycleBase140
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok157 : check start157 proof157 = true := by
  decide +kernel

theorem ok158 : check start158 proof158 = true := by
  decide +kernel

theorem ok159 : check start159 proof159 = true := by
  decide +kernel

theorem ok160 : andB (check start160 proof160) (cpOk (replay start160 proof160) start161) = true := by
  decide +kernel

end Snake9.LocalWindow.CycleBase140
