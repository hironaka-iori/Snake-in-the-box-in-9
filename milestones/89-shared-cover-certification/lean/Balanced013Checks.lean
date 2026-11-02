import Balanced013Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable013_valid : check boxTable013 = true := by decide +kernel

theorem boxTable013_flat : flatten boxTable013 = boxes013 := by decide +kernel

theorem balancedCover013 :
    checkCoverLookup advanceBalanced 833 (fun i => lookup boxTable013 i [])
      6 [] root013 tree013 = true := by decide +kernel

theorem originalCover013 :
    checkCover retainedDiagram boxes013 6 [] root013 tree013 = true := by
  apply lookup_cover_to_original advanceBalanced 833 (fun i => lookup boxTable013 i [])
    retainedDiagram boxes013 root013 tree013
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable013 boxes013 boxTable013_valid boxTable013_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover013

#print axioms boxTable013_valid
#print axioms boxTable013_flat
#print axioms balancedCover013
#print axioms originalCover013

end Snake9.Shared89
