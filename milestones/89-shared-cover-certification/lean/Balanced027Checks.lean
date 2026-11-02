import Balanced027Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable027_valid : check boxTable027 = true := by decide +kernel

theorem boxTable027_flat : flatten boxTable027 = boxes027 := by decide +kernel

theorem balancedCover027 :
    checkCoverLookup advanceBalanced 703 (fun i => lookup boxTable027 i [])
      6 [] root027 tree027 = true := by decide +kernel

theorem originalCover027 :
    checkCover retainedDiagram boxes027 6 [] root027 tree027 = true := by
  apply lookup_cover_to_original advanceBalanced 703 (fun i => lookup boxTable027 i [])
    retainedDiagram boxes027 root027 tree027
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable027 boxes027 boxTable027_valid boxTable027_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover027

#print axioms boxTable027_valid
#print axioms boxTable027_flat
#print axioms balancedCover027
#print axioms originalCover027

end Snake9.Shared89
