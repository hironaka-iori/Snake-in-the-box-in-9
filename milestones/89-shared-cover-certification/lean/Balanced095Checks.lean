import Balanced095Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable095_valid : check boxTable095 = true := by decide +kernel

theorem boxTable095_flat : flatten boxTable095 = boxes095 := by decide +kernel

theorem balancedCover095 :
    checkCoverLookup advanceBalanced 816 (fun i => lookup boxTable095 i [])
      6 [] root095 tree095 = true := by decide +kernel

theorem originalCover095 :
    checkCover retainedDiagram boxes095 6 [] root095 tree095 = true := by
  apply lookup_cover_to_original advanceBalanced 816 (fun i => lookup boxTable095 i [])
    retainedDiagram boxes095 root095 tree095
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable095 boxes095 boxTable095_valid boxTable095_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover095

#print axioms boxTable095_valid
#print axioms boxTable095_flat
#print axioms balancedCover095
#print axioms originalCover095

end Snake9.Shared89
