import LocalWindowUnsat.End35.Data57
import LocalWindowUnsat.End35.Data58

/-! Kernel checks of segments 337-342 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok337 : check start337 proof337 = true := by
  decide +kernel

theorem ok338 : check start338 proof338 = true := by
  decide +kernel

theorem ok339 : check start339 proof339 = true := by
  decide +kernel

theorem ok340 : check start340 proof340 = true := by
  decide +kernel

theorem ok341 : check start341 proof341 = true := by
  decide +kernel

theorem ok342 : andB (check start342 proof342) (cpOk (replay start342 proof342) start343) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
