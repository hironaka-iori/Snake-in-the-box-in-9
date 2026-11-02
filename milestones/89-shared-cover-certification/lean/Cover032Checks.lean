import Cover032Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover032 : checkCover retainedDiagram boxes032 6 [] root032 tree032 = true := by
  decide +kernel

#print axioms cover032
end Snake9.Shared89
