import Cover009Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover009 : checkCover retainedDiagram boxes009 6 [] root009 tree009 = true := by
  decide +kernel

#print axioms cover009
end Snake9.Shared89
