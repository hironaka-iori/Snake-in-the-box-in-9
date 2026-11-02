import Cover030Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover030 : checkCover retainedDiagram boxes030 6 [] root030 tree030 = true := by
  decide +kernel

#print axioms cover030
end Snake9.Shared89
