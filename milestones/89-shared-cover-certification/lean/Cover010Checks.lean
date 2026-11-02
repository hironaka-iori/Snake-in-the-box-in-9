import Cover010Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover010 : checkCover retainedDiagram boxes010 6 [] root010 tree010 = true := by
  decide +kernel

#print axioms cover010
end Snake9.Shared89
