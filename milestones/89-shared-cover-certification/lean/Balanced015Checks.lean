import Balanced015Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable015_valid : check boxTable015 = true := by decide +kernel

theorem boxTable015_flat : flatten boxTable015 = boxes015 := by decide +kernel

theorem balancedCover015 :
    checkCoverLookup advanceBalanced 676 (fun i => lookup boxTable015 i [])
      6 [] root015 tree015 = true := by decide +kernel

theorem originalCover015 :
    checkCover retainedDiagram boxes015 6 [] root015 tree015 = true := by
  apply lookup_cover_to_original advanceBalanced 676 (fun i => lookup boxTable015 i [])
    retainedDiagram boxes015 root015 tree015
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable015 boxes015 boxTable015_valid boxTable015_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover015

#print axioms boxTable015_valid
#print axioms boxTable015_flat
#print axioms balancedCover015
#print axioms originalCover015

end Snake9.Shared89
