import Recovered123G.LocalWindowUnsat.SixFour10.Data36
import Recovered123G.LocalWindowUnsat.SixFour10.Data37

/-! Kernel checks of segments 211-216 of `four10` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SixFour10
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok211 : check start211 proof211 = true := by
  decide +kernel

theorem ok212 : check start212 proof212 = true := by
  decide +kernel

theorem ok213 : check start213 proof213 = true := by
  decide +kernel

theorem ok214 : check start214 proof214 = true := by
  decide +kernel

theorem ok215 : check start215 proof215 = true := by
  decide +kernel

theorem ok216 : andB (check start216 proof216) (cpOk (replay start216 proof216) start217) = true := by
  decide +kernel

end Snake9.LocalWindow.SixFour10
