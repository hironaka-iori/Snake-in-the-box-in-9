import Balanced059Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable059_valid : check boxTable059 = true := by decide +kernel

theorem boxTable059_flat : flatten boxTable059 = boxes059 := by decide +kernel

theorem balancedCover059 :
    checkCoverLookup advanceBalanced 847 (fun i => lookup boxTable059 i [])
      6 [] root059 tree059 = true := by decide +kernel

theorem originalCover059 :
    checkCover retainedDiagram boxes059 6 [] root059 tree059 = true := by
  apply lookup_cover_to_original advanceBalanced 847 (fun i => lookup boxTable059 i [])
    retainedDiagram boxes059 root059 tree059
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable059 boxes059 boxTable059_valid boxTable059_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover059

#print axioms boxTable059_valid
#print axioms boxTable059_flat
#print axioms balancedCover059
#print axioms originalCover059

end Snake9.Shared89
