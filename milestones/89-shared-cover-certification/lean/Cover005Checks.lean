import Cover005Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover005 : checkCover retainedDiagram boxes005 6 [] root005 tree005 = true := by
  decide +kernel

#print axioms cover005
end Snake9.Shared89
