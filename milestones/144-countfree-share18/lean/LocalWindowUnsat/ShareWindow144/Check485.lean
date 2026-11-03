import LocalWindowUnsat.ShareWindow144.Data485
import LocalWindowUnsat.ShareWindow144.Data486

/-! Kernel checks of segments 1937-1940 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1937 : check start1937 proof1937 = true := by
  decide +kernel

theorem ok1938 : check start1938 proof1938 = true := by
  decide +kernel

theorem ok1939 : check start1939 proof1939 = true := by
  decide +kernel

theorem ok1940 : andB (check start1940 proof1940) (cpOk (replay start1940 proof1940) start1941) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
