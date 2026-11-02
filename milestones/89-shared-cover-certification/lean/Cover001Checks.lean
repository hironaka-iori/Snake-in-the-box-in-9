import Cover001Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover001 : checkCover retainedDiagram boxes001 6 [] root001 tree001 = true := by
  decide +kernel

#print axioms cover001
end Snake9.Shared89
