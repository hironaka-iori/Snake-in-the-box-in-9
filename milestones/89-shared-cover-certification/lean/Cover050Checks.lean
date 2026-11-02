import Cover050Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover050 : checkCover retainedDiagram boxes050 6 [] root050 tree050 = true := by
  decide +kernel

#print axioms cover050
end Snake9.Shared89
