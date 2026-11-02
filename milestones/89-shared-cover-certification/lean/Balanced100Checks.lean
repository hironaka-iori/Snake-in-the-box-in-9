import Balanced100Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable100_valid : check boxTable100 = true := by decide +kernel

theorem boxTable100_flat : flatten boxTable100 = boxes100 := by decide +kernel

theorem balancedCover100 :
    checkCoverLookup advanceBalanced 809 (fun i => lookup boxTable100 i [])
      6 [] root100 tree100 = true := by decide +kernel

theorem originalCover100 :
    checkCover retainedDiagram boxes100 6 [] root100 tree100 = true := by
  apply lookup_cover_to_original advanceBalanced 809 (fun i => lookup boxTable100 i [])
    retainedDiagram boxes100 root100 tree100
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable100 boxes100 boxTable100_valid boxTable100_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover100

#print axioms boxTable100_valid
#print axioms boxTable100_flat
#print axioms balancedCover100
#print axioms originalCover100

end Snake9.Shared89
