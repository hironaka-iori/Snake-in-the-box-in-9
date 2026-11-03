import LocalWindowUnsat.ShareWindow144.Data233
import LocalWindowUnsat.ShareWindow144.Data234

/-! Kernel checks of segments 929-932 of `share144` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.ShareWindow144
open Snake9.LratFast144
open Snake9.Lrat144 (Tree TreeTrue andB)

theorem ok929 : check start929 proof929 = true := by
  decide +kernel

theorem ok930 : check start930 proof930 = true := by
  decide +kernel

theorem ok931 : check start931 proof931 = true := by
  decide +kernel

theorem ok932 : andB (check start932 proof932) (cpOk (replay start932 proof932) start933) = true := by
  decide +kernel

end Snake9.LocalWindow.ShareWindow144
