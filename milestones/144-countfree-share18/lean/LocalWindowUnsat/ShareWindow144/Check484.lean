import LocalWindowUnsat.ShareWindow144.Data484
import LocalWindowUnsat.ShareWindow144.Data485

/-! Kernel checks of segments 1933-1936 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok1933 : check start1933 proof1933 = true := by
  decide +kernel

theorem ok1934 : check start1934 proof1934 = true := by
  decide +kernel

theorem ok1935 : check start1935 proof1935 = true := by
  decide +kernel

theorem ok1936 : andB (check start1936 proof1936) (cpOk (replay start1936 proof1936) start1937) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
