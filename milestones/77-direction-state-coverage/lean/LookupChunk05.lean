import LookupDefinitions
namespace Snake9.Direction77
open Snake9.WindowAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem direction_chunk_5 : allBelow 5 (fun i => (lookupCheck extensions) (500+i)) = true := by decide +kernel
#print axioms direction_chunk_5
theorem maps_chunk_5 : allBelow 5 (fun i => (mapCheck) (500+i)) = true := by decide +kernel
#print axioms maps_chunk_5
end Snake9.Direction77
