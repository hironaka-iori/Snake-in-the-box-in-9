import Balanced041Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable041_valid : check boxTable041 = true := by decide +kernel

theorem boxTable041_flat : flatten boxTable041 = boxes041 := by decide +kernel

theorem balancedCover041 :
    checkCoverLookup advanceBalanced 665 (fun i => lookup boxTable041 i [])
      6 [] root041 tree041 = true := by decide +kernel

theorem originalCover041 :
    checkCover retainedDiagram boxes041 6 [] root041 tree041 = true := by
  apply lookup_cover_to_original advanceBalanced 665 (fun i => lookup boxTable041 i [])
    retainedDiagram boxes041 root041 tree041
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable041 boxes041 boxTable041_valid boxTable041_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover041

#print axioms boxTable041_valid
#print axioms boxTable041_flat
#print axioms balancedCover041
#print axioms originalCover041

end Snake9.Shared89
