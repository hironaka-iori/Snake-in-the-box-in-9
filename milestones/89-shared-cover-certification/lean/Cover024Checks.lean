import Cover024Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover024 : checkCover retainedDiagram boxes024 6 [] root024 tree024 = true := by
  decide +kernel

#print axioms cover024
end Snake9.Shared89
