import Case000Data
import CoverageAssembly

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Certificate88
open Snake9.Boxes88 Snake9.Retained87

theorem witnesses000 : entriesValid 0 0 entries000 = true := by decide +kernel

theorem cover000 : checkCover retainedDiagram boxes000 6 [] root000 tree000 = true := by
  decide +kernel

theorem retained000 (code : Nat) (hc : code < 46656)
    (hkeep : numericKeep 0 0 code = true) :
    diagramEval retainedDiagram root000 (digits code) = true :=
  numeric_keep_implies_diagram 0 0 code retainedDiagram root000 entries000 tree000
    hc witnesses000 cover000 hkeep

#print axioms witnesses000
#print axioms cover000
#print axioms retained000
end Snake9.Certificate88
