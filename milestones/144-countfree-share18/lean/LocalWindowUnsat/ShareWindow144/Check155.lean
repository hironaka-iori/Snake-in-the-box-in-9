import LocalWindowUnsat.ShareWindow144.Data155
import LocalWindowUnsat.ShareWindow144.Data156

/-! Kernel checks of segments 617-620 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok617 : check start617 proof617 = true := by
  decide +kernel

theorem ok618 : check start618 proof618 = true := by
  decide +kernel

theorem ok619 : check start619 proof619 = true := by
  decide +kernel

theorem ok620 : andB (check start620 proof620) (cpOk (replay start620 proof620) start621) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
