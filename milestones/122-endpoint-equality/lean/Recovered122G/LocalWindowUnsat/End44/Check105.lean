import Recovered122G.LocalWindowUnsat.End44.Data105

/-! Kernel checks of segments 625-630 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok625 : check start625 proof625 = true := by
  decide +kernel

theorem ok626 : check start626 proof626 = true := by
  decide +kernel

theorem ok627 : check start627 proof627 = true := by
  decide +kernel

theorem ok628 : check start628 proof628 = true := by
  decide +kernel

theorem ok629 : check start629 proof629 = true := by
  decide +kernel

theorem ok630 : andB (check start630 proof630) (hasEmpty (replay start630 proof630) 4096) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
