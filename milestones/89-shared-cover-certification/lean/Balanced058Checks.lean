import Balanced058Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable058_valid : check boxTable058 = true := by decide +kernel

theorem boxTable058_flat : flatten boxTable058 = boxes058 := by decide +kernel

theorem balancedCover058 :
    checkCoverLookup advanceBalanced 822 (fun i => lookup boxTable058 i [])
      6 [] root058 tree058 = true := by decide +kernel

theorem originalCover058 :
    checkCover retainedDiagram boxes058 6 [] root058 tree058 = true := by
  apply lookup_cover_to_original advanceBalanced 822 (fun i => lookup boxTable058 i [])
    retainedDiagram boxes058 root058 tree058
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable058 boxes058 boxTable058_valid boxTable058_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover058

#print axioms boxTable058_valid
#print axioms boxTable058_flat
#print axioms balancedCover058
#print axioms originalCover058

end Snake9.Shared89
