import Cover100Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem cover100 : checkCover retainedDiagram boxes100 6 [] root100 tree100 = true := by
  decide +kernel

#print axioms cover100
end Snake9.Shared89
