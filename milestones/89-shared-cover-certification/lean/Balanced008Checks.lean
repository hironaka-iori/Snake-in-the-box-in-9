import Balanced008Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable008_valid : check boxTable008 = true := by decide +kernel

theorem boxTable008_flat : flatten boxTable008 = boxes008 := by decide +kernel

theorem balancedCover008 :
    checkCoverLookup advanceBalanced 779 (fun i => lookup boxTable008 i [])
      6 [] root008 tree008 = true := by decide +kernel

theorem originalCover008 :
    checkCover retainedDiagram boxes008 6 [] root008 tree008 = true := by
  apply lookup_cover_to_original advanceBalanced 779 (fun i => lookup boxTable008 i [])
    retainedDiagram boxes008 root008 tree008
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable008 boxes008 boxTable008_valid boxTable008_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover008

#print axioms boxTable008_valid
#print axioms boxTable008_flat
#print axioms balancedCover008
#print axioms originalCover008

end Snake9.Shared89
