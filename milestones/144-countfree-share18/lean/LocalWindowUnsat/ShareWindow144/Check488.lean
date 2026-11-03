import LocalWindowUnsat.ShareWindow144.Data488
import LocalWindowUnsat.ShareWindow144.Data489

/-! Kernel checks of segments 1949-1952 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1949 : check start1949 proof1949 = true := by
  decide +kernel

theorem ok1950 : check start1950 proof1950 = true := by
  decide +kernel

theorem ok1951 : check start1951 proof1951 = true := by
  decide +kernel

theorem ok1952 : andB (check start1952 proof1952) (cpOk (replay start1952 proof1952) start1953) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
