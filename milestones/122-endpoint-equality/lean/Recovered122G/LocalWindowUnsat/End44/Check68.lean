import Recovered122G.LocalWindowUnsat.End44.Data68
import Recovered122G.LocalWindowUnsat.End44.Data69

/-! Kernel checks of segments 403-408 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok403 : check start403 proof403 = true := by
  decide +kernel

theorem ok404 : check start404 proof404 = true := by
  decide +kernel

theorem ok405 : check start405 proof405 = true := by
  decide +kernel

theorem ok406 : check start406 proof406 = true := by
  decide +kernel

theorem ok407 : check start407 proof407 = true := by
  decide +kernel

theorem ok408 : andB (check start408 proof408) (cpOk (replay start408 proof408) start409) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
