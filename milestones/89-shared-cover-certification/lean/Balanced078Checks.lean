import Balanced078Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable078_valid : check boxTable078 = true := by decide +kernel

theorem boxTable078_flat : flatten boxTable078 = boxes078 := by decide +kernel

theorem balancedCover078 :
    checkCoverLookup advanceBalanced 605 (fun i => lookup boxTable078 i [])
      6 [] root078 tree078 = true := by decide +kernel

theorem originalCover078 :
    checkCover retainedDiagram boxes078 6 [] root078 tree078 = true := by
  apply lookup_cover_to_original advanceBalanced 605 (fun i => lookup boxTable078 i [])
    retainedDiagram boxes078 root078 tree078
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable078 boxes078 boxTable078_valid boxTable078_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover078

#print axioms boxTable078_valid
#print axioms boxTable078_flat
#print axioms balancedCover078
#print axioms originalCover078

end Snake9.Shared89
