import Cover101Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover101 : checkCover retainedDiagram boxes101 6 [] root101 tree101 = true := by
  decide +kernel

#print axioms cover101
end Snake9.Shared89
