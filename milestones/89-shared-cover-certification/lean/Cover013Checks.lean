import Cover013Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover013 : checkCover retainedDiagram boxes013 6 [] root013 tree013 = true := by
  decide +kernel

#print axioms cover013
end Snake9.Shared89
