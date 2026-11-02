import Cover006Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover006 : checkCover retainedDiagram boxes006 6 [] root006 tree006 = true := by
  decide +kernel

#print axioms cover006
end Snake9.Shared89
