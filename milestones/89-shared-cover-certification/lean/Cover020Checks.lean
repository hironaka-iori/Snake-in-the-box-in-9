import Cover020Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover020 : checkCover retainedDiagram boxes020 6 [] root020 tree020 = true := by
  decide +kernel

#print axioms cover020
end Snake9.Shared89
