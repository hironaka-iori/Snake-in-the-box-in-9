import Balanced007Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable007_valid : check boxTable007 = true := by decide +kernel

theorem boxTable007_flat : flatten boxTable007 = boxes007 := by decide +kernel

theorem balancedCover007 :
    checkCoverLookup advanceBalanced 581 (fun i => lookup boxTable007 i [])
      6 [] root007 tree007 = true := by decide +kernel

theorem originalCover007 :
    checkCover retainedDiagram boxes007 6 [] root007 tree007 = true := by
  apply lookup_cover_to_original advanceBalanced 581 (fun i => lookup boxTable007 i [])
    retainedDiagram boxes007 root007 tree007
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable007 boxes007 boxTable007_valid boxTable007_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover007

#print axioms boxTable007_valid
#print axioms boxTable007_flat
#print axioms balancedCover007
#print axioms originalCover007

end Snake9.Shared89
