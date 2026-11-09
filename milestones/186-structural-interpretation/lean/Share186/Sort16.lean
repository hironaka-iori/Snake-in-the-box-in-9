import Share186.EndpointData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem ep_sort16 : pw epVerts16 = true := by decide +kernel
#print axioms ep_sort16
theorem ep_cross16 : epVerts16.all (fun x => (epVerts17).all (fun y => decide (x < y))) = true := by decide +kernel
#print axioms ep_cross16
end Snake9.LocalWindow.ShareWindow185
