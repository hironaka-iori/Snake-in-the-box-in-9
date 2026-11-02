import Balanced076Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable076_valid : check boxTable076 = true := by decide +kernel

theorem boxTable076_flat : flatten boxTable076 = boxes076 := by decide +kernel

theorem balancedCover076 :
    checkCoverLookup advanceBalanced 717 (fun i => lookup boxTable076 i [])
      6 [] root076 tree076 = true := by decide +kernel

theorem originalCover076 :
    checkCover retainedDiagram boxes076 6 [] root076 tree076 = true := by
  apply lookup_cover_to_original advanceBalanced 717 (fun i => lookup boxTable076 i [])
    retainedDiagram boxes076 root076 tree076
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable076 boxes076 boxTable076_valid boxTable076_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover076

#print axioms boxTable076_valid
#print axioms boxTable076_flat
#print axioms balancedCover076
#print axioms originalCover076

end Snake9.Shared89
