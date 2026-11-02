import Cover002Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover002 : checkCover retainedDiagram boxes002 6 [] root002 tree002 = true := by
  decide +kernel

#print axioms cover002
end Snake9.Shared89
