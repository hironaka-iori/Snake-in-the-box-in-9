import Cover026Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover026 : checkCover retainedDiagram boxes026 6 [] root026 tree026 = true := by
  decide +kernel

#print axioms cover026
end Snake9.Shared89
