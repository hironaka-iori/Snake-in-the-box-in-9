import LocalWindowUnsat.End44.Data103
import LocalWindowUnsat.End44.Data104

/-! Kernel checks of segments 613-618 of `end44` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.End44
open Snake9.LratFastEndpoint122
open Snake9.Lrat (Tree TreeTrue andB)

theorem ok613 : check start613 proof613 = true := by
  decide +kernel

theorem ok614 : check start614 proof614 = true := by
  decide +kernel

theorem ok615 : check start615 proof615 = true := by
  decide +kernel

theorem ok616 : check start616 proof616 = true := by
  decide +kernel

theorem ok617 : check start617 proof617 = true := by
  decide +kernel

theorem ok618 : andB (check start618 proof618) (cpOk (replay start618 proof618) start619) = true := by
  decide +kernel

end Snake9.LocalWindow.End44
