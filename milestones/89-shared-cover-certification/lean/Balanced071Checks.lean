import Balanced071Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable071_valid : check boxTable071 = true := by decide +kernel

theorem boxTable071_flat : flatten boxTable071 = boxes071 := by decide +kernel

theorem balancedCover071 :
    checkCoverLookup advanceBalanced 332 (fun i => lookup boxTable071 i [])
      6 [] root071 tree071 = true := by decide +kernel

theorem originalCover071 :
    checkCover retainedDiagram boxes071 6 [] root071 tree071 = true := by
  apply lookup_cover_to_original advanceBalanced 332 (fun i => lookup boxTable071 i [])
    retainedDiagram boxes071 root071 tree071
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable071 boxes071 boxTable071_valid boxTable071_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover071

#print axioms boxTable071_valid
#print axioms boxTable071_flat
#print axioms balancedCover071
#print axioms originalCover071

end Snake9.Shared89
