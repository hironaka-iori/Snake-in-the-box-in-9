import Balanced111Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable111_valid : check boxTable111 = true := by decide +kernel

theorem boxTable111_flat : flatten boxTable111 = boxes111 := by decide +kernel

theorem balancedCover111 :
    checkCoverLookup advanceBalanced 657 (fun i => lookup boxTable111 i [])
      6 [] root111 tree111 = true := by decide +kernel

theorem originalCover111 :
    checkCover retainedDiagram boxes111 6 [] root111 tree111 = true := by
  apply lookup_cover_to_original advanceBalanced 657 (fun i => lookup boxTable111 i [])
    retainedDiagram boxes111 root111 tree111
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable111 boxes111 boxTable111_valid boxTable111_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover111

#print axioms boxTable111_valid
#print axioms boxTable111_flat
#print axioms balancedCover111
#print axioms originalCover111

end Snake9.Shared89
