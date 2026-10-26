import LocalWindowUnsat.SharePressure513.Data6
import LocalWindowUnsat.SharePressure513.Data7
import LocalWindowUnsat.SharePressure513.Data8
import LocalWindowUnsat.SharePressure513.Data9
import LocalWindowUnsat.SharePressure513.Data10
import LocalWindowUnsat.SharePressure513.Data11
import LocalWindowUnsat.SharePressure513.Data12

/-! Kernel checks of segments 7-12 of `share3_47` (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option Elab.async false

namespace Snake9.LocalWindow.SharePressure513
open Snake9.LratFastO5k14
open Snake9.LratO5k (Tree TreeTrue andB)

theorem ok7 : check start7 proof7 = true := by
  decide +kernel

theorem ok8 : andB (check start8 proof8) (cpOk (replay start8 proof8) start9) = true := by
  decide +kernel

theorem ok9 : check start9 proof9 = true := by
  decide +kernel

theorem ok10 : check start10 proof10 = true := by
  decide +kernel

theorem ok11 : check start11 proof11 = true := by
  decide +kernel

theorem ok12 : andB (check start12 proof12) (hasEmpty (replay start12 proof12) 4096) = true := by
  decide +kernel

end Snake9.LocalWindow.SharePressure513
