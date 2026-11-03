import LocalWindowUnsat.ShareWindow144.Data307
import LocalWindowUnsat.ShareWindow144.Data308

/-! Kernel checks of segments 1225-1228 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1225 : check start1225 proof1225 = true := by
  decide +kernel

theorem ok1226 : check start1226 proof1226 = true := by
  decide +kernel

theorem ok1227 : check start1227 proof1227 = true := by
  decide +kernel

theorem ok1228 : andB (check start1228 proof1228) (cpOk (replay start1228 proof1228) start1229) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
