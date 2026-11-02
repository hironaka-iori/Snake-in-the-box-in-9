import Cover003Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover003 : checkCover retainedDiagram boxes003 6 [] root003 tree003 = true := by
  decide +kernel

#print axioms cover003
end Snake9.Shared89
