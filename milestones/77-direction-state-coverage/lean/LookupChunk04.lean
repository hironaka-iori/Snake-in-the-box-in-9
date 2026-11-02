import LookupDefinitions
namespace Snake9.Direction77
open Snake9.WindowAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem direction_chunk_4 : allBelow 100 (fun i => (lookupCheck extensions) (400+i)) = true := by decide +kernel
#print axioms direction_chunk_4
theorem maps_chunk_4 : allBelow 100 (fun i => (mapCheck) (400+i)) = true := by decide +kernel
#print axioms maps_chunk_4
end Snake9.Direction77
