import LocalWindowUnsat.ShareWindow144.Data492
import LocalWindowUnsat.ShareWindow144.Data493

/-! Kernel checks of segments 1965-1968 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1965 : check start1965 proof1965 = true := by
  decide +kernel

theorem ok1966 : check start1966 proof1966 = true := by
  decide +kernel

theorem ok1967 : check start1967 proof1967 = true := by
  decide +kernel

theorem ok1968 : andB (check start1968 proof1968) (cpOk (replay start1968 proof1968) start1969) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
