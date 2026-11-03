import LocalWindowUnsat.ShareWindow144.Data334
import LocalWindowUnsat.ShareWindow144.Data335

/-! Kernel checks of segments 1333-1336 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1333 : check start1333 proof1333 = true := by
  decide +kernel

theorem ok1334 : check start1334 proof1334 = true := by
  decide +kernel

theorem ok1335 : check start1335 proof1335 = true := by
  decide +kernel

theorem ok1336 : andB (check start1336 proof1336) (cpOk (replay start1336 proof1336) start1337) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
