import Recovered129G.LocalWindowUnsat.Triple129.Data81
import Recovered129G.LocalWindowUnsat.Triple129.Data82

/-! Kernel checks of segments 321-324 of `triple129` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.Triple129
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok321 : check start321 proof321 = true := by
  decide +kernel

theorem ok322 : check start322 proof322 = true := by
  decide +kernel

theorem ok323 : check start323 proof323 = true := by
  decide +kernel

theorem ok324 : andB (check start324 proof324) (cpOk (replay start324 proof324) start325) = true := by
  decide +kernel

end Snake9.LocalWindow.Triple129
