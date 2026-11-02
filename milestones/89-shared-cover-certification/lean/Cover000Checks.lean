import Cover000Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover000 : checkCover retainedDiagram boxes000 6 [] root000 tree000 = true := by
  decide +kernel

#print axioms cover000
end Snake9.Shared89
