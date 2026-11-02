import Cover060Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover060 : checkCover retainedDiagram boxes060 6 [] root060 tree060 = true := by
  decide +kernel

#print axioms cover060
end Snake9.Shared89
