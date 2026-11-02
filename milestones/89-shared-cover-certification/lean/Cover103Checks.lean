import Cover103Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover103 : checkCover retainedDiagram boxes103 6 [] root103 tree103 = true := by
  decide +kernel

#print axioms cover103
end Snake9.Shared89
