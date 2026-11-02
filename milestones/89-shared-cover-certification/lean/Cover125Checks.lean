import Cover125Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover125 : checkCover retainedDiagram boxes125 6 [] root125 tree125 = true := by
  decide +kernel

#print axioms cover125
end Snake9.Shared89
