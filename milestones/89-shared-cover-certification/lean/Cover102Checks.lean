import Cover102Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover102 : checkCover retainedDiagram boxes102 6 [] root102 tree102 = true := by
  decide +kernel

#print axioms cover102
end Snake9.Shared89
