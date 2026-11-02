import Cover004Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover004 : checkCover retainedDiagram boxes004 6 [] root004 tree004 = true := by
  decide +kernel

#print axioms cover004
end Snake9.Shared89
