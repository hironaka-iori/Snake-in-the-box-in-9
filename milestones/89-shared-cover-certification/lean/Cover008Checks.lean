import Cover008Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover008 : checkCover retainedDiagram boxes008 6 [] root008 tree008 = true := by
  decide +kernel

#print axioms cover008
end Snake9.Shared89
