import Balanced023Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable023_valid : check boxTable023 = true := by decide +kernel

theorem boxTable023_flat : flatten boxTable023 = boxes023 := by decide +kernel

theorem balancedCover023 :
    checkCoverLookup advanceBalanced 491 (fun i => lookup boxTable023 i [])
      6 [] root023 tree023 = true := by decide +kernel

theorem originalCover023 :
    checkCover retainedDiagram boxes023 6 [] root023 tree023 = true := by
  apply lookup_cover_to_original advanceBalanced 491 (fun i => lookup boxTable023 i [])
    retainedDiagram boxes023 root023 tree023
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable023 boxes023 boxTable023_valid boxTable023_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover023

#print axioms boxTable023_valid
#print axioms boxTable023_flat
#print axioms balancedCover023
#print axioms originalCover023

end Snake9.Shared89
