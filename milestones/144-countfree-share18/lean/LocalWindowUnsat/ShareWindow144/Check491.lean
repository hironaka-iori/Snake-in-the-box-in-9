import LocalWindowUnsat.ShareWindow144.Data491
import LocalWindowUnsat.ShareWindow144.Data492

/-! Kernel checks of segments 1961-1964 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1961 : check start1961 proof1961 = true := by
  decide +kernel

theorem ok1962 : check start1962 proof1962 = true := by
  decide +kernel

theorem ok1963 : check start1963 proof1963 = true := by
  decide +kernel

theorem ok1964 : andB (check start1964 proof1964) (cpOk (replay start1964 proof1964) start1965) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
