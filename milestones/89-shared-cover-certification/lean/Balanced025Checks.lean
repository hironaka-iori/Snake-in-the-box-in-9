import Balanced025Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable025_valid : check boxTable025 = true := by decide +kernel

theorem boxTable025_flat : flatten boxTable025 = boxes025 := by decide +kernel

theorem balancedCover025 :
    checkCoverLookup advanceBalanced 424 (fun i => lookup boxTable025 i [])
      6 [] root025 tree025 = true := by decide +kernel

theorem originalCover025 :
    checkCover retainedDiagram boxes025 6 [] root025 tree025 = true := by
  apply lookup_cover_to_original advanceBalanced 424 (fun i => lookup boxTable025 i [])
    retainedDiagram boxes025 root025 tree025
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable025 boxes025 boxTable025_valid boxTable025_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover025

#print axioms boxTable025_valid
#print axioms boxTable025_flat
#print axioms balancedCover025
#print axioms originalCover025

end Snake9.Shared89
