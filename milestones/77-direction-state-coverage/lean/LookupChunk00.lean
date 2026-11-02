import LookupDefinitions
namespace Snake9.Direction77
open Snake9.WindowAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shape_roundtrip : allBelow 132 (lookupCheck shapes) = true := by decide +kernel
#print axioms shape_roundtrip
theorem direction_chunk_0 : allBelow 100 (fun i => (lookupCheck extensions) (0+i)) = true := by decide +kernel
#print axioms direction_chunk_0
theorem maps_chunk_0 : allBelow 100 (fun i => (mapCheck) (0+i)) = true := by decide +kernel
#print axioms maps_chunk_0
end Snake9.Direction77
