import Cover025Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover025 : checkCover retainedDiagram boxes025 6 [] root025 tree025 = true := by
  decide +kernel

#print axioms cover025
end Snake9.Shared89
