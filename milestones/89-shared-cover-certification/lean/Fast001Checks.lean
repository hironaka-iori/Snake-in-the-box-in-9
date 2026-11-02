import Cover001Data
import ArrayCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

theorem arrayCover001 :
    checkCoverArray retainedDiagram boxes001.toArray 6 [] root001 tree001 = true := by
  decide +kernel

theorem listCover001 :
    checkCover retainedDiagram boxes001 6 [] root001 tree001 = true :=
  array_cover_to_list retainedDiagram boxes001 root001 tree001 arrayCover001

#print axioms arrayCover001
#print axioms listCover001
end Snake9.Shared89
