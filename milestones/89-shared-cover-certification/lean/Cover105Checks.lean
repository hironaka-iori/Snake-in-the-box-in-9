import Cover105Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover105 : checkCover retainedDiagram boxes105 6 [] root105 tree105 = true := by
  decide +kernel

#print axioms cover105
end Snake9.Shared89
