import Cover065Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover065 : checkCover retainedDiagram boxes065 6 [] root065 tree065 = true := by
  decide +kernel

#print axioms cover065
end Snake9.Shared89
