import Cover023Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover023 : checkCover retainedDiagram boxes023 6 [] root023 tree023 = true := by
  decide +kernel

#print axioms cover023
end Snake9.Shared89
