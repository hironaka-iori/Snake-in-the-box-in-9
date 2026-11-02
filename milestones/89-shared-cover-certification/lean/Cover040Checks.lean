import Cover040Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover040 : checkCover retainedDiagram boxes040 6 [] root040 tree040 = true := by
  decide +kernel

#print axioms cover040
end Snake9.Shared89
