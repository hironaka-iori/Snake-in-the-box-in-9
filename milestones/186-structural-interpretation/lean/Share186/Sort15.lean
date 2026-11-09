import Share186.EndpointData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem ep_sort15 : pw epVerts15 = true := by decide +kernel
#print axioms ep_sort15
theorem ep_cross15 : epVerts15.all (fun x => (epVerts16 ++ epVerts17).all (fun y => decide (x < y))) = true := by decide +kernel
#print axioms ep_cross15
end Snake9.LocalWindow.ShareWindow185
