import LocalWindowUnsat.End35.Data54
import LocalWindowUnsat.End35.Data55

/-! Kernel checks of segments 319-324 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok319 : check start319 proof319 = true := by
  decide +kernel

theorem ok320 : check start320 proof320 = true := by
  decide +kernel

theorem ok321 : check start321 proof321 = true := by
  decide +kernel

theorem ok322 : check start322 proof322 = true := by
  decide +kernel

theorem ok323 : check start323 proof323 = true := by
  decide +kernel

theorem ok324 : andB (check start324 proof324) (cpOk (replay start324 proof324) start325) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
