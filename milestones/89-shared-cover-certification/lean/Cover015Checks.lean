import Cover015Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover015 : checkCover retainedDiagram boxes015 6 [] root015 tree015 = true := by
  decide +kernel

#print axioms cover015
end Snake9.Shared89
