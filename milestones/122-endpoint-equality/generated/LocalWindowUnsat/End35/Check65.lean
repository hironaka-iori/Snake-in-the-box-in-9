import LocalWindowUnsat.End35.Data65
import LocalWindowUnsat.End35.Data66

/-! Kernel checks of segments 385-390 of `end35` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End35
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok385 : check start385 proof385 = true := by
  decide +kernel

theorem ok386 : check start386 proof386 = true := by
  decide +kernel

theorem ok387 : check start387 proof387 = true := by
  decide +kernel

theorem ok388 : check start388 proof388 = true := by
  decide +kernel

theorem ok389 : check start389 proof389 = true := by
  decide +kernel

theorem ok390 : andB (check start390 proof390) (cpOk (replay start390 proof390) start391) = true := by
  decide +kernel

end Snake9.LocalWindow.End35
