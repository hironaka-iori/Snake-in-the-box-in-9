import Share186.EndpointData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem ep_sort3 : pw epVerts3 = true := by decide +kernel
#print axioms ep_sort3
theorem ep_cross3 : epVerts3.all (fun x => (epVerts4 ++ epVerts5 ++ epVerts6 ++ epVerts7 ++ epVerts8 ++ epVerts9 ++ epVerts10 ++ epVerts11 ++ epVerts12 ++ epVerts13 ++ epVerts14 ++ epVerts15 ++ epVerts16 ++ epVerts17).all (fun y => decide (x < y))) = true := by decide +kernel
#print axioms ep_cross3
end Snake9.LocalWindow.ShareWindow185
