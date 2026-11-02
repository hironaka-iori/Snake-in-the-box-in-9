import Balanced087Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable087_valid : check boxTable087 = true := by decide +kernel

theorem boxTable087_flat : flatten boxTable087 = boxes087 := by decide +kernel

theorem balancedCover087 :
    checkCoverLookup advanceBalanced 636 (fun i => lookup boxTable087 i [])
      6 [] root087 tree087 = true := by decide +kernel

theorem originalCover087 :
    checkCover retainedDiagram boxes087 6 [] root087 tree087 = true := by
  apply lookup_cover_to_original advanceBalanced 636 (fun i => lookup boxTable087 i [])
    retainedDiagram boxes087 root087 tree087
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable087 boxes087 boxTable087_valid boxTable087_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover087

#print axioms boxTable087_valid
#print axioms boxTable087_flat
#print axioms balancedCover087
#print axioms originalCover087

end Snake9.Shared89
