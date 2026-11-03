import Recovered122G.LocalWindowUnsat.End44.Data104
import Recovered122G.LocalWindowUnsat.End44.Data105

/-! Kernel checks of segments 619-624 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok619 : check start619 proof619 = true := by
  decide +kernel

theorem ok620 : check start620 proof620 = true := by
  decide +kernel

theorem ok621 : check start621 proof621 = true := by
  decide +kernel

theorem ok622 : check start622 proof622 = true := by
  decide +kernel

theorem ok623 : check start623 proof623 = true := by
  decide +kernel

theorem ok624 : andB (check start624 proof624) (cpOk (replay start624 proof624) start625) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
